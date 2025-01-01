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

module P = Printf

let interactive = ref false

let opts =
  [ ("-interactive", Arg.Set interactive, "Run with interactive mode") ]

let usage = ""
let file = ref ""

let args f =
  if Sys.file_exists f then file := f
  else raise (Arg.Bad (f ^ ": No such file"))

let dump_nodes chan l =
  List.iter
    (fun (node, attr) ->
      match attr with
      | `List [ cmd; `Bool loophead; `Bool callnode ] ->
          let cmd = Yojson.Safe.to_string cmd in
          let cmd =
            if String.length cmd > 2 then
              String.sub cmd 1 (String.length cmd - 2)
            else ""
          in
          let str =
            node ^ "[label=\"" ^ node ^ ": " ^ cmd ^ "\""
            ^ (if loophead then " style=filled color=lightblue" else "")
            ^ (if callnode then " style=filled color=grey" else "")
            ^ "]\n"
          in
          output_string chan str
      | _ -> raise (Failure "error"))
    l;
  Printf.fprintf chan "}\n"

let dump_edges chan l =
  List.iter
    (fun edge ->
      match edge with
      | `List [ `String v1; `String v2 ] ->
          Printf.fprintf chan "%s -> %s\n" v1 v2
      | _ -> raise (Failure "error"))
    l

let dump_dug chan pid l dug =
  List.iter
    (fun (src, _) ->
      List.iter
        (fun (dst, _) ->
          try
            let psrc, pdst = (pid ^ "-" ^ src, pid ^ "-" ^ dst) in
            let label = BatMap.find (psrc, pdst) dug in
            Printf.fprintf chan "%s -> %s [label=\"%s\" color=red]\n" src dst
              label
            (* Printf.fprintf chan "%s -> %s [tooltip=\"%s\" color=red]\n" src dst label*)
          with _ -> ())
        l)
    l

let dump_cfgs = function
  | `Assoc l ->
      List.iter
        (fun (pid, cfg) ->
          let dot = pid ^ ".dot" in
          let chan = open_out dot in
          Printf.fprintf chan "digraph %s {\n" pid;
          Printf.fprintf chan "{\n";
          Printf.fprintf chan "node [shape=box]\n";
          (match cfg with
          | `Assoc [ (_, `Assoc nodes); (_, `List edges) ] ->
              dump_nodes chan nodes;
              dump_edges chan edges
          | _ -> raise (Failure "error"));
          Printf.fprintf chan "}\n";
          close_out chan;
          let _ =
            Unix.create_process "dot"
              [| "dot"; "-Tsvg"; "-o" ^ pid ^ ".svg"; dot |]
              Unix.stdin Unix.stdout Unix.stderr
          in
          let _ = Unix.wait () in
          ())
        l
  | _ -> raise (Failure "Invalid json format")

let dump_cfgs_with_dug json dug =
  Printf.printf "Dump control flow graphs...\n";
  flush stdout;
  match json with
  | `Assoc l ->
      List.iter
        (fun (pid, cfg) ->
          let dot = pid ^ ".dot" in
          let chan = open_out dot in
          Printf.fprintf chan "digraph %s {\n" pid;
          Printf.fprintf chan "{\n";
          Printf.fprintf chan "node [shape=box]\n";
          (match cfg with
          | `Assoc [ (_, `Assoc nodes); ("edges", `List edges); _ ] ->
              dump_nodes chan nodes;
              dump_edges chan edges;
              dump_dug chan pid nodes dug
          | _ -> raise (Failure "error"));
          Printf.fprintf chan "}\n";
          close_out chan;
          let _ =
            Unix.create_process "dot"
              [| "dot"; "-Tsvg"; "-o" ^ pid ^ ".svg"; dot |]
              Unix.stdin Unix.stdout Unix.stderr
          in
          let _ = Unix.wait () in
          ())
        l
  | _ -> raise (Failure "Invalid json format")

let dump_callgraph json =
  Printf.printf "Dump call graph...\n";
  flush stdout;
  let index = "callgraph.dot" in
  let chan = open_out index in
  Printf.fprintf chan "digraph %s {\n" "callgraph";
  Printf.fprintf chan "{\n";
  Printf.fprintf chan "node [shape=box]\n";
  (match json with
  | `Assoc l -> (
      match (List.assoc "nodes" l, List.assoc "edges" l) with
      | `List nodes, `List edges ->
          List.iter
            (fun node ->
              match node with
              | `String s ->
                  Printf.fprintf chan "%s[label=\"%s\" URL=\"%s\"]\n" s s
                    (s ^ ".svg")
              | _ -> raise (Failure "error"))
            nodes;
          Printf.fprintf chan "}\n";
          List.iter
            (fun edge ->
              match edge with
              | `List [ `String v1; `String v2 ] ->
                  Printf.fprintf chan "%s -> %s\n" v1 v2
              | _ -> raise (Failure "error"))
            edges;
          Printf.fprintf chan "}\n"
      | _ -> raise (Failure "Invalid json format"))
  | _ -> raise (Failure "Invalid json format"));
  close_out chan;
  let _ =
    Unix.create_process "dot"
      [| "dot"; "-Tsvg"; "-ocallgraph.svg"; index |]
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _ = Unix.wait () in
  ()

let create_index () =
  let index = "index.html" in
  let chan = open_out index in
  Printf.fprintf chan "<html>\n";
  Printf.fprintf chan "<head>\n";
  Printf.fprintf chan
    "<meta http-equiv=\"refresh\" content=\"0; url=callgraph.svg\" />";
  Printf.fprintf chan "</head>\n";
  Printf.fprintf chan "<body>\n";
  Printf.fprintf chan "</body>\n";
  Printf.fprintf chan "</html>\n";
  close_out chan

let gen_dug = function
  | `Assoc dug -> (
      let edges = List.assoc "edges" dug in
      match edges with
      | `List l ->
          List.fold_left
            (fun m e ->
              match e with
              | `List [ `String src; `String dst; `String label ] ->
                  BatMap.add (src, dst) label m
              | _ -> m)
            BatMap.empty l
      | _ -> raise (Failure "error"))
  | _ -> raise (Failure "error")

let dump json =
  let dir = Filename.dirname !file ^ "/vis" in
  (try Unix.mkdir dir 0o755 with _ -> ());
  Unix.chdir dir;
  create_index ();
  match json with
  | `Assoc global ->
      let dug =
        try gen_dug (List.assoc "dugraph" global) with _ -> BatMap.empty
      in
      dump_callgraph (List.assoc "callgraph" global);
      dump_cfgs_with_dug (List.assoc "cfgs" global) dug
  | _ -> raise (Failure "error")

module DUGraph = ItvAnalysis.DUGraph
module PowLoc = DUGraph.PowLoc
module Loc = PowLoc.A
module Node = BasicDom.Node

let history_filename = ".sparrow-vis-history.txt"

let initialize () =
  LNoise.history_load ~filename:history_filename |> ignore;
  LNoise.history_set ~max_length:100 |> ignore;
  LNoise.set_completion_callback (fun line_so_far ln_completions ->
      if line_so_far <> "" && line_so_far.[0] = 'c' then
        [ "common" ] |> List.iter (LNoise.add_completion ln_completions))

let cmd_exit () =
  flush_all ();
  exit 0

module PowNode = BasicDom.PowNode

type env = { filename : string; global : Global.t; dug : DUGraph.t }

let rec slice allocs pc workset allocsites dug new_dug =
  if PowNode.is_empty workset then new_dug
  else
    let work, workset = PowNode.pop workset in
    let workset, new_dug =
      DUGraph.fold_pred
        (fun p (workset, new_dug) ->
          if List.exists (fun alloc -> DUGraph.check_path pc p alloc) allocs
          then
            let filtered =
              DUGraph.get_abslocs p work dug
              |> DUGraph.PowLoc.filter (fun x ->
                     List.mem (Loc.to_string x) allocsites)
            in
            if PowLoc.is_empty filtered then (workset, new_dug)
            else
              let workset =
                if DUGraph.mem_node p new_dug then workset
                else PowNode.add p workset
              in
              (workset, DUGraph.add_abslocs p filtered work new_dug)
          else (workset, new_dug))
        dug work (workset, new_dug)
    in
    slice allocs pc workset allocsites dug new_dug

let cmd_common { filename; dug; _ } alarm allocsites =
  let allocsite_nodes =
    List.map
      (fun x -> DUGraph.find_node_of_string dug x |> Option.get)
      allocsites
  in
  let alarm = DUGraph.find_node_of_string dug alarm |> Option.get in
  let nodes =
    List.fold_left
      (fun nodes alloc ->
        DUGraph.shortest_path_loc_str dug alloc alarm (Node.to_string alloc)
        |> BasicDom.PowNode.of_list
        |> BasicDom.PowNode.union nodes)
      BasicDom.PowNode.empty allocsite_nodes
  in
  PowNode.iter (fun x -> prerr_endline (BasicDom.Node.to_string x)) nodes;
  let path_checker = DUGraph.create_path_checker dug in
  let dug =
    slice allocsite_nodes path_checker (PowNode.singleton alarm) allocsites dug
      (DUGraph.create ())
  in
  let dirname = Filename.dirname filename in
  let basename =
    Filename.basename filename |> Fun.flip Filename.chop_suffix ".bin"
  in
  let filename = Filename.concat dirname basename in
  let oc = open_out (filename ^ ".dot") in
  let color =
    (alarm, "red") :: List.map (fun x -> (x, "cyan")) allocsite_nodes
  in
  P.fprintf oc "%s\n" (DUGraph.to_dot ~color dug);
  close_out oc;
  Unix.create_process "dot"
    [| "dot"; "-Tsvg"; "-o"; filename ^ ".svg"; filename ^ ".dot" |]
    Unix.stdin Unix.stdout Unix.stderr
  |> ignore;
  Unix.wait () |> ignore;
  P.printf "Done\n";
  P.printf "#nodes     = %d\n" (DUGraph.nb_node dug);
  P.printf "#edges     = %d\n" (DUGraph.nb_edge dug);
  P.printf "#abs locs  = %d\n" (DUGraph.nb_loc dug)

let cmd_all { global; dug; _ } =
  P.printf "#nodes     = %d\n" (DUGraph.nb_node dug);
  P.printf "#edges     = %d\n" (DUGraph.nb_edge dug);
  P.printf "#abs locs  = %d\n" (DUGraph.nb_loc dug);
  let json = ItvAnalysis.Analysis.to_json (global, dug) in
  dump json

let cmd_cfgs { global; _ } =
  let json = ItvAnalysis.Analysis.to_json (global, DUGraph.create ()) in
  dump json

let cmd_functions { global; dug; _ } functions =
  let new_dug = DUGraph.copy dug in
  let new_dug =
    DUGraph.fold_node
      (fun node new_dug ->
        if List.mem (Node.pid node) functions then dug
        else DUGraph.remove_node node new_dug)
      dug new_dug
  in
  P.printf "#nodes     = %d\n" (DUGraph.nb_node dug);
  P.printf "#edges     = %d\n" (DUGraph.nb_edge dug);
  P.printf "#abs locs  = %d\n" (DUGraph.nb_loc dug);
  let json = ItvAnalysis.Analysis.to_json (global, new_dug) in
  dump json

let cmd_help () =
  P.printf
    "    all                                          : draw the full dugraph\n";
  P.printf "    cfgs                                         : draw cfgs only\n";
  P.printf
    "    functions [func1] [func2] ... [funcN]        : draw a dugraph only \
     for given functions\n";
  P.printf
    "    common [alarm] [allocsite1] [allocsite2] ... : draw a common subgraph\n"

let repl env cmd =
  let components = Str.split (Str.regexp "[ \t]+") cmd in
  match components with
  | [ "all" ] -> cmd_all env
  | [ "cfgs" ] -> cmd_cfgs env
  | "functions" :: fns -> cmd_functions env fns
  | "common" :: alarm :: allocsites -> cmd_common env alarm allocsites
  | [ "help" ] -> cmd_help ()
  | [ "exit" ] -> cmd_exit ()
  | _ -> P.eprintf "Invalid command\nTry help\n"

let rec user_input prompt env cb =
  match LNoise.linenoise prompt with
  | None -> ()
  | Some v ->
      repl env v;
      flush_all ();
      cb v;
      user_input prompt env cb
  | exception Sys.Break -> cmd_exit ()

let dump_bin filename =
  let ic = open_in filename in
  let dug = Marshal.from_channel ic in
  close_in ic;
  let ic = open_in (Filename.dirname filename ^ "/global.bin") in
  let global = Marshal.from_channel ic in
  close_in ic;
  let env = { filename; global; dug } in
  P.printf "Processing...\n";
  P.printf "#nodes     = %d\n" (DUGraph.nb_node dug);
  P.printf "#edges     = %d\n" (DUGraph.nb_edge dug);
  P.printf "#abs locs  = %d\n" (DUGraph.nb_loc dug);
  flush_all ();
  initialize ();
  (fun from_user ->
    LNoise.history_add from_user |> ignore;
    LNoise.history_save ~filename:history_filename |> ignore)
  |> user_input "visualizer> " env

let main () =
  Arg.parse opts args usage;
  Printf.printf "Reading the input file...\n";
  if Filename.check_suffix !file ".json" then
    Yojson.Safe.from_file !file |> dump
  else if Filename.check_suffix !file ".bin" then dump_bin !file
  else
    let _ = Printf.eprintf "Unknown file type" in
    exit 1

let _ = main ()
