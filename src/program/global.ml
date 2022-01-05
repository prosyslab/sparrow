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

open Vocab
open BasicDom
open InterCfg
module L = Logging

type t = {
  file : Cil.file;
  icfg : InterCfg.t;
  callgraph : CallGraph.t;
  dump : Dump.t;
  mem : ItvDom.Mem.t;
  table : ItvDom.Table.t;
  relations : RelSemantics.Set.t;
}

let remove_node node global =
  { global with icfg = InterCfg.remove_node node global.icfg }

let remove_function pid global =
  {
    global with
    icfg = InterCfg.remove_function pid global.icfg;
    callgraph = CallGraph.remove_function pid global.callgraph;
    dump = Dump.remove pid global.dump;
  }

let is_rec pid global = CallGraph.is_rec global.callgraph pid

let remove_unreachable_nodes global =
  let nodes_all = InterCfg.nodesof global.icfg in
  let unreachable = InterCfg.unreachable_node global.icfg in
  let global = NodeSet.fold remove_node unreachable global in
  L.info ~level:1 "\n%-14s: %d\n" "#nodes all" (List.length nodes_all);
  L.info ~level:1 "%-14s: %d\n" "#unreachable" (NodeSet.cardinal unreachable);
  global

let remove_unreachable_functions global =
  let pids_all = PowProc.of_list (InterCfg.pidsof global.icfg) in
  let reachable =
    CallGraph.trans_callees InterCfg.global_proc global.callgraph
    |> BatSet.fold PowProc.add !Options.keep_unreachable_from
    |> BatSet.fold
         (fun f rset ->
           CallGraph.trans_callees f global.callgraph |> PowProc.join rset)
         !Options.keep_unreachable_from
  in
  let unreachable =
    PowProc.diff pids_all reachable |> PowProc.remove InterCfg.global_proc
  in
  let recursive = PowProc.filter (fun pid -> is_rec pid global) reachable in
  let global =
    if !Options.bugfinder >= 2 then global
    else PowProc.fold remove_function unreachable global
  in
  L.info ~level:1 "%-16s: %d\n" "#functions all" (PowProc.cardinal pids_all);
  L.info ~level:1 "%-16s: %d\n" "#recursive" (PowProc.cardinal recursive);
  if PowProc.cardinal recursive > 0 then
    L.info ~level:1 "%a\n" PowProc.pp recursive;
  L.info ~level:1 "%-16s: %d\n" "#unreachable" (PowProc.cardinal unreachable);
  if PowProc.cardinal unreachable > 0 then
    L.info ~level:1 "%a\n" PowProc.pp unreachable;
  global

let init file =
  {
    file;
    icfg = InterCfg.init file;
    callgraph = CallGraph.empty ();
    dump = Dump.empty;
    mem = ItvDom.Mem.bot;
    table = ItvDom.Table.bot;
    relations = RelSemantics.Set.empty;
  }
  |> if !Options.keep_unreachable then id else remove_unreachable_nodes

let is_undef pid global = InterCfg.is_undef pid global.icfg

let get_leaf_procs global =
  let pids = PowProc.of_list (InterCfg.pidsof global.icfg) in
  PowProc.fold
    (fun fid ->
      if PowProc.cardinal (CallGraph.trans_callees fid global.callgraph) = 1
      then PowProc.add fid
      else id)
    pids PowProc.bot

let to_json g =
  `Assoc
    [
      ("callgraph", CallGraph.to_json g.callgraph);
      ("cfgs", InterCfg.to_json g.icfg);
    ]

let print_json chan g = Yojson.Safe.pretty_to_channel chan (to_json g)
