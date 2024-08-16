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
open ProsysCil
module L = Logging

type t = {
  file : Cil.file;
  icfg : InterCfg.t;
  callgraph : CallGraph.t;
  dump : Dump.t;
  mem : ItvDom.Mem.t;
  table : ItvDom.Table.t;
  relations : RelSemantics.Set.t;
  line_to_func : (string, string) BatMap.t;
  cyclic_calls : (pid * pid) BatSet.t;
}

let remove_nodes nodes global =
  { global with icfg = NodeSet.fold InterCfg.remove_node nodes global.icfg }

let remove_functions pids global =
  let folder pid glob =
    {
      glob with
      icfg = InterCfg.remove_function pid glob.icfg;
      callgraph = CallGraph.remove_function pid glob.callgraph;
      dump = Dump.remove pid glob.dump;
    }
  in
  let global = PowProc.fold folder pids global in
  { global with callgraph = CallGraph.compute_transitive global.callgraph }

let is_rec pid global = CallGraph.is_rec global.callgraph pid

let remove_unreachable_nodes global =
  let nodes_all = InterCfg.nodesof global.icfg in
  let unreachable = InterCfg.unreachable_node global.icfg in
  let global = remove_nodes unreachable global in
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
    else remove_functions unreachable global
  in
  L.info ~level:1 "%-16s: %d\n" "#functions all" (PowProc.cardinal pids_all);
  L.info ~level:1 "%-16s: %d\n" "#reachable"
    (PowProc.cardinal pids_all - PowProc.cardinal unreachable);
  L.info ~level:1 "%-16s: %d\n" "#unreachable" (PowProc.cardinal unreachable);
  if PowProc.cardinal unreachable > 0 then
    L.info ~level:1 "%a\n" PowProc.pp unreachable;
  L.info ~level:1 "%-16s: %d\n" "#recursive" (PowProc.cardinal recursive);
  if PowProc.cardinal recursive > 0 then
    L.info ~level:1 "%a\n" PowProc.pp recursive;
  global

let handle_cyclic_call global =
  let cyclic_calls = CallGraph.find_back_edges global.callgraph |> list2set in
  L.info "List of cyclic call edges:\n";
  BatSet.iter (fun (src, dst) -> L.info "%s -> %s\n" src dst) cyclic_calls;
  let folder (src, dst) acc_cg = CallGraph.remove_edge src dst acc_cg in
  let callgraph = BatSet.fold folder cyclic_calls global.callgraph in
  let callgraph = CallGraph.compute_transitive callgraph in
  let icfg = global.icfg in
  let folder (src, dst) acc_icfg =
    let src_nodes =
      InterCfg.nodes_of_pid icfg src
      |> List.filter (fun n -> InterCfg.is_callnode n icfg)
    in
    list_fold (fun n g -> InterCfg.remove_call_edge n dst g) src_nodes acc_icfg
  in
  let icfg = BatSet.fold folder cyclic_calls icfg in
  { global with cyclic_calls; callgraph; icfg }

(* Record the original function names so we can retrieve them after inline *)
let build_line_to_func_map global =
  let nodes = InterCfg.nodesof global.icfg in
  let folder acc n =
    BatMap.add (InterCfg.node_to_lstr global.icfg n) (Node.get_pid n) acc
  in
  let line_to_func = List.fold_left folder BatMap.empty nodes in
  { global with line_to_func }

let init file =
  {
    file;
    icfg = InterCfg.init file;
    callgraph = CallGraph.empty ();
    dump = Dump.empty;
    mem = ItvDom.Mem.bot;
    table = ItvDom.Table.bot;
    relations = RelSemantics.Set.empty;
    line_to_func = BatMap.empty;
    cyclic_calls = BatSet.empty;
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
