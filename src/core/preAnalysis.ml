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
open Global
open BasicDom
open ItvDom
module L = Logging

(* ***************************** *
 * Flow-insensitive pre-analysis *
 * ***************************** *)
let onestep_transfer nodes (mem, global) =
  list_fold
    (fun node (mem, global) ->
      ItvSem.run AbsSem.Weak ItvSem.Spec.empty node (mem, global))
    nodes (mem, global)

let rec fixpt nodes k (mem, global) =
  my_prerr_string ("\riteration : " ^ string_of_int k);
  flush stderr;
  let mem', global' = onestep_transfer nodes (mem, global) in
  let mem' = Mem.widen mem mem' in
  if Mem.le mem' mem && Dump.le global'.dump global.dump then (
    L.info ~level:1 "#iteration : %d\n" k;
    (mem', global'))
  else if !Options.max_pre_iter > 0 && !Options.max_pre_iter = k then (
    L.info ~level:1 "#iteration : %d (unsound)\n" k;
    (mem', global'))
  else fixpt nodes (k + 1) (mem', global')

let callees_of icfg node mem =
  let pid = InterCfg.Node.pid node in
  let c = InterCfg.cmd_of icfg node in
  match c with
  | IntraCfg.Cmd.Ccall (_, e, _, _) ->
      Val.pow_proc_of_val (ItvSem.eval pid e mem)
  | _ -> PowProc.bot

let draw_call_edges nodes mem global =
  let icfg =
    List.fold_left
      (fun icfg node ->
        if InterCfg.is_call_node node icfg then
          let callees = callees_of icfg node mem in
          PowProc.fold (InterCfg.add_call_edge node) callees icfg
        else icfg)
      global.icfg nodes
  in
  { global with icfg }

let draw_callgraph nodes mem global =
  let callgraph =
    List.fold_left
      (fun callgraph node ->
        let callees = callees_of global.icfg node mem in
        PowProc.fold
          (fun callee callgraph ->
            CallGraph.add_edge (InterCfg.Node.pid node) callee callgraph)
          callees callgraph)
      global.callgraph nodes
    |> CallGraph.compute_transitive
  in
  { global with callgraph }

let perform global =
  let nodes = InterCfg.nodes_of global.icfg in
  let mem, global = fixpt nodes 1 (Mem.bot, global) in
  L.info ~level:1 "mem size : %d\n\n" (Mem.cardinal mem);
  { global with mem } |> draw_call_edges nodes mem |> draw_callgraph nodes mem
  |> opt (not !Options.keep_unreachable) Global.remove_unreachable_functions
  |> opt !Options.cut_cyclic_call Global.handle_cyclic_call
