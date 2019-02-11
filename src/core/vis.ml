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

let opts = []

let usage = ""

let file = ref ""

let args f =
  if Sys.file_exists f then file := f
  else raise (Arg.Bad (f ^ ": No such file"))

let dump_nodes chan l =
  List.iter
    (fun (node, attr) ->
      match attr with
      | `List [cmd; `Bool loophead; `Bool callnode] ->
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
      | _ -> raise (Failure "error") )
    l ;
  Printf.fprintf chan "}\n"

let dump_edges chan l =
  List.iter
    (fun edge ->
      match edge with
      | `List [`String v1; `String v2] ->
          Printf.fprintf chan "%s -> %s\n" v1 v2
      | _ -> raise (Failure "error") )
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
          with _ -> () )
        l )
    l

let dump_cfgs = function
  | `Assoc l ->
      List.iter
        (fun (pid, cfg) ->
          let dot = pid ^ ".dot" in
          let chan = open_out dot in
          Printf.fprintf chan "digraph %s {\n" pid ;
          Printf.fprintf chan "{\n" ;
          Printf.fprintf chan "node [shape=box]\n" ;
          ( match cfg with
          | `Assoc [(_, `Assoc nodes); (_, `List edges)] ->
              dump_nodes chan nodes ; dump_edges chan edges
          | _ -> raise (Failure "error") ) ;
          Printf.fprintf chan "}\n" ;
          close_out chan ;
          let _ =
            Unix.create_process "dot"
              [|"dot"; "-Tsvg"; "-o" ^ pid ^ ".svg"; dot|]
              Unix.stdin Unix.stdout Unix.stderr
          in
          let _ = Unix.wait () in
          () )
        l
  | _ -> raise (Failure "Invalid json format")

let dump_cfgs_with_dug json dug =
  match json with
  | `Assoc l ->
      List.iter
        (fun (pid, cfg) ->
          let dot = pid ^ ".dot" in
          let chan = open_out dot in
          Printf.fprintf chan "digraph %s {\n" pid ;
          Printf.fprintf chan "{\n" ;
          Printf.fprintf chan "node [shape=box]\n" ;
          ( match cfg with
          | `Assoc [(_, `Assoc nodes); (_, `List edges)] ->
              dump_nodes chan nodes ;
              dump_edges chan edges ;
              dump_dug chan pid nodes dug
          | _ -> raise (Failure "error") ) ;
          Printf.fprintf chan "}\n" ;
          close_out chan ;
          let _ =
            Unix.create_process "dot"
              [|"dot"; "-Tsvg"; "-o" ^ pid ^ ".svg"; dot|]
              Unix.stdin Unix.stdout Unix.stderr
          in
          let _ = Unix.wait () in
          () )
        l
  | _ -> raise (Failure "Invalid json format")

let dump_callgraph json =
  let index = "callgraph.dot" in
  let chan = open_out index in
  Printf.fprintf chan "digraph %s {\n" "callgraph" ;
  Printf.fprintf chan "{\n" ;
  Printf.fprintf chan "node [shape=box]\n" ;
  ( match json with
  | `Assoc l -> (
    match (List.assoc "nodes" l, List.assoc "edges" l) with
    | `List nodes, `List edges ->
        List.iter
          (fun node ->
            match node with
            | `String s ->
                Printf.fprintf chan "%s[label=\"%s\" URL=\"%s\"]\n" s s
                  (s ^ ".svg")
            | _ -> raise (Failure "error") )
          nodes ;
        Printf.fprintf chan "}\n" ;
        List.iter
          (fun edge ->
            match edge with
            | `List [`String v1; `String v2] ->
                Printf.fprintf chan "%s -> %s\n" v1 v2
            | _ -> raise (Failure "error") )
          edges ;
        Printf.fprintf chan "}\n"
    | _ -> raise (Failure "Invalid json format") )
  | _ -> raise (Failure "Invalid json format") ) ;
  close_out chan ;
  let _ =
    Unix.create_process "dot"
      [|"dot"; "-Tsvg"; "-ocallgraph.svg"; index|]
      Unix.stdin Unix.stdout Unix.stderr
  in
  let _ = Unix.wait () in
  ()

let create_index () =
  let index = "index.html" in
  let chan = open_out index in
  Printf.fprintf chan "<html>\n" ;
  Printf.fprintf chan "<head>\n" ;
  Printf.fprintf chan
    "<meta http-equiv=\"refresh\" content=\"0; url=callgraph.svg\" />" ;
  Printf.fprintf chan "</head>\n" ;
  Printf.fprintf chan "<body>\n" ;
  Printf.fprintf chan "</body>\n" ;
  Printf.fprintf chan "</html>\n" ;
  close_out chan

let gen_dug = function
  | `Assoc dug -> (
      let edges = List.assoc "edges" dug in
      match edges with
      | `List l ->
          List.fold_left
            (fun m e ->
              match e with
              | `List [`String src; `String dst; `String label] ->
                  BatMap.add (src, dst) label m
              | _ -> m )
            BatMap.empty l
      | _ -> raise (Failure "error") )
  | _ -> raise (Failure "error")

let dump json =
  let dir = !file ^ ".vis" in
  (try Unix.mkdir dir 0o755 with _ -> ()) ;
  Unix.chdir dir ;
  create_index () ;
  match json with
  | `Assoc global ->
      let dug =
        try gen_dug (List.assoc "dugraph" global) with _ -> BatMap.empty
      in
      dump_callgraph (List.assoc "callgraph" global) ;
      dump_cfgs_with_dug (List.assoc "cfgs" global) dug
  | _ -> raise (Failure "error")

let main () =
  Arg.parse opts args usage ;
  let json = Yojson.Safe.from_file !file in
  dump json

let _ = main ()
