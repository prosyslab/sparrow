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
module L = Logging

(* ************************************************************************* *
 * Pre-processing to approximate recursive functions and reachable functions *
 * ************************************************************************* *)

(* Functions related to call-graph construction *)

let collect_call_from_cmd icfg node acc_calls =
  match InterCfg.cmdof icfg node with
  | IntraCfg.Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, _) ->
      if InterCfg.is_undef f.vname icfg then acc_calls
      else BatSet.add (node, f.vname) acc_calls
  | _ -> acc_calls

let find_direct_calls icfg =
  let folder = collect_call_from_cmd icfg in
  let all_nodes = InterCfg.nodesof icfg in
  list_fold folder all_nodes BatSet.empty

let approximate_call_graph global =
  let call_edges = find_direct_calls global.icfg in
  let folder (caller_node, callee_func) (icfg, callgraph) =
    let caller_func = InterCfg.Node.get_pid caller_node in
    ( InterCfg.add_call_edge caller_node callee_func icfg,
      CallGraph.add_edge caller_func callee_func callgraph )
  in
  let init = (global.icfg, global.callgraph) in
  let icfg, callgraph = BatSet.fold folder call_edges init in
  let callgraph = CallGraph.compute_transitive callgraph in
  { global with icfg; callgraph }

(* Functions related to finding references *)

let rec collect_fref_from_exp icfg gvar_map exp =
  match exp with
  | Cil.Const _ -> PowProc.empty
  | Cil.Lval l | Cil.StartOf l | Cil.AddrOf l ->
      collect_fref_from_lv icfg gvar_map l
  | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ -> PowProc.empty
  | Cil.AlignOf _ | Cil.AlignOfE _ -> PowProc.empty
  | Cil.UnOp (_, e, _) | Cil.CastE (_, e) ->
      collect_fref_from_exp icfg gvar_map e
  | Cil.BinOp (_, e1, e2, _) | Cil.Question (_, e1, e2, _) ->
      PowProc.union
        (collect_fref_from_exp icfg gvar_map e1)
        (collect_fref_from_exp icfg gvar_map e2)
  | Cil.AddrOfLabel _ -> PowProc.empty

and collect_fref_from_lv icfg gvar_map lv =
  match fst lv with
  | Cil.Var v ->
      if InterCfg.is_def v.vname icfg then PowProc.singleton v.vname
      else if BatMap.mem v.vname gvar_map then BatMap.find v.vname gvar_map
      else PowProc.empty
  | Cil.Mem e -> collect_fref_from_exp icfg gvar_map e

let weak_add k v m is_fixed =
  let prev_v = if BatMap.mem k m then BatMap.find k m else PowProc.empty in
  let new_v = PowProc.union v prev_v in
  (BatMap.add k new_v m, is_fixed && PowProc.subset v prev_v)

let update_gvar_fref_map icfg node (acc_map, acc_flag) =
  match InterCfg.cmdof icfg node with
  | IntraCfg.Cmd.Cset ((Cil.Var v, _), e, _) ->
      let frefs = collect_fref_from_exp icfg acc_map e in
      if PowProc.is_empty frefs then (acc_map, acc_flag)
      else weak_add v.vname frefs acc_map acc_flag
  | IntraCfg.Cmd.Ccall
      ( _,
        Cil.Lval (Cil.Var f, Cil.NoOffset),
        Cil.Lval (Cil.Var v, _) :: real_arg_exps,
        _ )
    when f.vname = "sparrow_array_init" ->
      let frefs =
        List.map (collect_fref_from_exp icfg acc_map) real_arg_exps
        |> List.fold_left PowProc.union PowProc.empty
      in
      if PowProc.is_empty frefs then (acc_map, acc_flag)
      else weak_add v.vname frefs acc_map acc_flag
  | _ -> (acc_map, acc_flag)

(* Build a mapping from global variables to function references that can be held
 * by that reference. We target declaration statements like "handler = f;" or
 * "callback_table = { f, g, NULL };" that can found in _G_(). *)
let build_gvar_fref_map icfg =
  let folder = update_gvar_fref_map icfg in
  let g_nodes = InterCfg.nodes_of_pid icfg InterCfg.global_proc in
  let rec fixpt gvar_map =
    let gvar_map, is_fixed = list_fold folder g_nodes (gvar_map, true) in
    if is_fixed then gvar_map else fixpt gvar_map
  in
  fixpt BatMap.empty

let collect_fref_from_cmd icfg gvar_map node acc_frefs =
  match InterCfg.cmdof icfg node with
  | IntraCfg.Cmd.Cset (_, e, _) ->
      PowProc.union (collect_fref_from_exp icfg gvar_map e) acc_frefs
  | IntraCfg.Cmd.Ccall (_, f_exp, arg_exps, _) ->
      List.map (collect_fref_from_exp icfg gvar_map) arg_exps
      |> List.fold_left PowProc.union PowProc.empty
      |> PowProc.union (collect_fref_from_exp icfg gvar_map f_exp)
      |> PowProc.union acc_frefs
  | IntraCfg.Cmd.Creturn (Some e, _) ->
      PowProc.union (collect_fref_from_exp icfg gvar_map e) acc_frefs
  | _ -> acc_frefs

let collect_fref_from_func icfg gvar_map f =
  let folder = collect_fref_from_cmd icfg gvar_map in
  let f_nodes = InterCfg.nodes_of_pid icfg f in
  list_fold folder f_nodes PowProc.empty

let rec find_func_refs_loop icfg gvar_map acc_frefs visited = function
  | [] -> acc_frefs
  | head_func :: tail_funcs ->
      let frefs = collect_fref_from_func icfg gvar_map head_func in
      let acc_frefs = PowProc.union frefs acc_frefs in
      let to_add = PowProc.diff frefs visited in
      let visited = PowProc.union frefs visited in
      let worklist = PowProc.elements to_add @ tail_funcs in
      find_func_refs_loop icfg gvar_map acc_frefs visited worklist

(* Collect function references transitively, starting from entry (e.g. main).
 * Note that we don't start from _G_ because it contains global variable
 * declarations that may not be used in anyreachable function. Thus, we build
 * a map from global variable to its function references and use it during the
 * traversal. *)
let find_func_refs icfg =
  let gvar_map = build_gvar_fref_map icfg in
  let worklist = [ !Options.entry_point ] in
  (* _G_ and entry point must be added manually. *)
  find_func_refs_loop icfg gvar_map PowProc.empty PowProc.empty worklist
  |> PowProc.add InterCfg.global_proc
  |> PowProc.add !Options.entry_point

let remove_unreferred_funcs global =
  let frefs = find_func_refs global.icfg in
  let pids_all = PowProc.of_list (InterCfg.pidsof global.icfg) in
  let unrefs = PowProc.diff pids_all frefs in
  let recursive = PowProc.filter (fun pid -> is_rec pid global) frefs in
  L.info ~level:1 "%-16s: %d\n" "#functions all" (PowProc.cardinal pids_all);
  L.info ~level:1 "%-16s: %d\n" "#referred" (PowProc.cardinal frefs);
  if PowProc.cardinal frefs > 0 then L.info ~level:1 "%a\n" PowProc.pp frefs;
  L.info ~level:1 "%-16s: %d\n" "#unreferred" (PowProc.cardinal unrefs);
  if PowProc.cardinal unrefs > 0 then L.info ~level:1 "%a\n" PowProc.pp unrefs;
  L.info ~level:1 "%-16s: %d\n" "#recursive" (PowProc.cardinal recursive);
  if PowProc.cardinal recursive > 0 then
    L.info ~level:1 "%a\n" PowProc.pp recursive;
  Global.remove_functions unrefs global

let perform global =
  approximate_call_graph global
  |> opt (not !Options.keep_unreachable) remove_unreferred_funcs
