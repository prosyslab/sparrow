(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
open Cil
open Vocab
open Global
module C = Cil
module F = Frontc
module E = Errormsg
module L = Logging

let files = ref []

let marshal_file = ref ""

let args f =
  if !Options.task = Options.Capture then
    Options.build_commands := !Options.build_commands @ [ f ]
  else if Sys.file_exists f then
    if Filename.check_suffix f ".i" || Filename.check_suffix f ".c" then
      files := f :: !files
    else
      let _ = prerr_endline ("Error: " ^ f ^ ": Not a preprocessed C") in
      exit 1
  else
    let _ = prerr_endline ("Error: " ^ f ^ ": No such file") in
    exit 1

let parse_arg arg =
  if !Arg.current = 1 then
    match arg with
    | "capture" ->
        Options.options := Options.capture_opts;
        Options.task := Options.Capture
    | "analyze" ->
        Options.options := Options.opts;
        Options.task := Options.Analyze
    | _ -> args arg
  else args arg

let parseOneFile fname =
  (* PARSE and convert to CIL *)
  if !Cilutil.printStages then ignore (E.log "Parsing %s\n" fname);
  let cil = F.parse fname () in
  if not (Feature.enabled "epicenter") then Rmtmps.removeUnusedTemps cil;
  cil

let parse_internal files =
  match !Options.frontend with
  | Options.Cil -> List.map parseOneFile files
  | Options.Claml -> List.map ClamlFrontend.parse files
  | _ ->
      let _ = List.iter ClangFrontend.parse files in
      List.map
        (fun fname ->
          let target =
            Filename.concat
              (Filename.concat !Options.outdir "preprocess")
              (Filename.basename fname ^ ".bin")
          in
          let ic = open_in target in
          let cil = Marshal.from_channel ic in
          close_in ic;
          if not (Feature.enabled "epicenter") then Rmtmps.removeUnusedTemps cil;
          cil)
        files

let parse () =
  match parse_internal !files with
  | [ one ] -> one
  | [] ->
      prerr_endline "Error: No arguments are given";
      exit 1
  | files ->
      Mergecil.ignore_merge_conflicts := true;
      let merged = Stats.time "merge" (Mergecil.merge files) "merged" in
      if !E.hadErrors then E.s (E.error "There were errors during merging");
      merged

let makeCFGinfo f =
  ignore (Partial.calls_end_basic_blocks f);
  ignore (Partial.globally_unique_vids f);
  Cil.iterGlobals f (fun glob ->
      match glob with
      | Cil.GFun (fd, _) ->
          Cil.prepareCFG fd;
          (* jc: blockinggraph depends on this "true" arg *)
          ignore (Cil.computeCFGInfo fd true)
      | _ -> ());
  f

(* true if the given function has variable number of arguments *)
let is_varargs fid file =
  Cil.foldGlobals file
    (fun b global ->
      match global with
      | GFun (fd, _) when fd.svar.vname = fid -> (
          match fd.svar.vtype with TFun (_, _, b_va, _) -> b_va | _ -> b)
      | _ -> b)
    false

let inline global =
  let f = global.file in
  let regexps =
    List.map (fun str -> Str.regexp (".*" ^ str ^ ".*")) !Options.inline
  in
  let to_inline =
    list_fold
      (fun global to_inline ->
        match global with
        | GFun (fd, _)
          when List.exists
                 (fun regexp -> Str.string_match regexp fd.svar.vname 0)
                 regexps ->
            fd.svar.vname :: to_inline
        | _ -> to_inline)
      f.globals []
  in
  let varargs_procs = List.filter (fun fid -> is_varargs fid f) to_inline in
  let recursive_procs =
    List.filter (fun fid -> Global.is_rec fid global) to_inline
  in
  let large_procs =
    List.filter
      (fun fid ->
        try
          List.length (InterCfg.nodes_of_pid global.icfg fid)
          > !Options.inline_size
        with _ -> false)
      to_inline
  in
  let to_exclude = varargs_procs @ recursive_procs @ large_procs in
  L.info "To inline : %s\n" (Vocab.string_of_list Vocab.id to_inline);
  L.info "Excluded variable-arguments functions : %s\n"
    (Vocab.string_of_list Vocab.id varargs_procs);
  L.info "Excluded recursive functions : %s\n"
    (Vocab.string_of_list Vocab.id recursive_procs);
  L.info "Excluded too large functions : %s\n"
    (Vocab.string_of_list Vocab.id large_procs);
  Inline.toinline :=
    List.filter (fun fid -> not (List.mem fid to_exclude)) to_inline;
  Inline.doit f;
  not (!Inline.toinline = [])
