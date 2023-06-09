open Vocab
open Global
open BasicDom
open SlicingUtils
open DefUse
module L = Logging
module PowAlloc = PowDom.MakeCPO (BasicDom.Allocsite)
module Val = ItvDom.Val
module Mem = ItvDom.Mem
module AccessAnalysis = AccessAnalysis.Make (AccessSem.SlicingSem)
module Access = AccessAnalysis.Access
module DUGraph = Dug.Make (Access)
module SsaDug = SsaDug.Make (DUGraph)

let memoize = Hashtbl.create 10000

(* Check if the given location is live (valid) at the current point. *)
let rec is_accessible is_ret callee trans_caller reachable_alloc = function
  | Loc.GVar _ -> true
  | Loc.LVar (p, v, _) ->
      PowProc.mem p trans_caller
      || (is_ret && v = Loc.return_var_name && PowProc.mem p callee)
  | Loc.Allocsite (Local n) -> PowProc.mem (Node.get_pid n) trans_caller
  | Loc.Allocsite a -> PowAlloc.mem a reachable_alloc
  | Loc.Field (l, _, _) ->
      is_accessible is_ret callee trans_caller reachable_alloc l

(* Compute transitive caller when the current function is 'f' and call context
 * is 'ctx'. Note that the last element in 'f :: ctx' is the function where we
 * started to trace into a callee function. *)
let compute_trans_callers f ctx callgraph =
  let rec expand = function
    | [] -> failwith "Unreachable"
    | [ x ] -> PowProc.add x (CallGraph.trans_callers x callgraph)
    | head :: tail -> PowProc.add head (expand tail)
  in
  expand (f :: ctx)

let construct_dug global slicing_targets =
  let iterator (_, targ_str) = SlicingUtils.register_target global targ_str in
  List.iter iterator slicing_targets;
  let locset = ItvAnalysis.get_locset global.mem in
  (* We do not use semantics function to compute DU *)
  let dummy_sem _ (mem, global) = (mem, global) in
  let f_access = AccessAnalysis.perform global locset dummy_sem in
  let access = StepManager.stepf false "Access Analysis" f_access global.mem in
  let init = (global, access, locset) in
  let dug = StepManager.stepf false "DUG construction" SsaDug.make init in
  prerr_memory_usage ();
  dug

let initialize global targ_nodes =
  let slice = SliceDFG.init targ_nodes in
  let folder n (acc_visited, acc_works) =
    let uses = eval_use_of_targ global global.mem n in
    Printf.printf "Uses of %s: %s\n"
      (node_to_lstr_verbose global n)
      (PowLoc.to_string uses);
    SliceDFG.update_use_map n uses slice;
    (VisitLog.add n uses acc_visited, (n, uses) :: acc_works)
  in
  let visited, works = NodeSet.fold folder targ_nodes (VisitLog.empty, []) in
  (slice, visited, works)

let update_works node forward used visited works =
  let visited, new_fwds = VisitLog.update node forward visited in
  let visited, new_uses = VisitLog.update node used visited in
  let has_fwd = not (PowLoc.is_empty new_fwds) in
  let has_use = not (PowLoc.is_empty new_uses) in
  let works = if has_fwd then (node, new_fwds) :: works else works in
  let works = if has_use then (node, new_uses) :: works else works in
  (visited, works)

(* Note that transfer function for a call node is subsumed here *)
let transfer_normal global ctx node uses p (slice, visited, works) =
  let is_callee = not (is_list_empty ctx) in
  let node_f = InterCfg.Node.get_pid node in
  let p_f = InterCfg.Node.get_pid p in
  let _ =
    if node_f <> p_f then
      Printf.printf "Function changes: p_f = %s node_f = %s, uses = %s\n" p_f
        node_f (PowLoc.to_string uses)
  in
  let pred_du = eval_def_use global global.mem p in
  let forward = PowLoc.diff uses pred_du.defs in
  let defined = PowLoc.inter uses pred_du.defs in
  let used = DefUseInfo.lookup_defs defined pred_du in
  let slice =
    if is_callee then
      if PowLoc.is_empty defined then slice
      else SliceDFG.add_sliced_node p slice
    else
      SliceDFG.draw_edge_fwd p node forward slice
      |> SliceDFG.draw_edge_def p node defined used
  in
  let visited, works = update_works p forward used visited works in
  (slice, visited, works)

let skip_ret global node uses p (slice, visited, works) =
  let caller = InterCfg.Node.get_pid node in
  let callee = InterCfg.Node.get_pid p in
  let _ =
    Printf.printf "From %s (%s), ignore return from %s()\n"
      (node_to_lstr global node) caller callee
  in
  let call_node = InterCfg.callof node global.icfg in
  let slice = SliceDFG.draw_edge_fwd call_node node uses slice in
  let visited, works = update_works call_node uses PowLoc.empty visited works in
  (slice, visited, works)

(* Find out which locations were used by this callee to define 'uses' *)
let rec find_callee_use global dug ctx uses exit_node slice =
  let callee = InterCfg.Node.get_pid exit_node in
  if Hashtbl.mem memoize (callee, uses) then
    let u = Hashtbl.find memoize (callee, uses) in
    (u, slice)
  else
    let visited = VisitLog.add exit_node uses VisitLog.empty in
    let works = [ (exit_node, uses) ] in
    let u, slice =
      trace_callee global dug ctx callee PowLoc.empty slice visited works
    in
    let _ = Hashtbl.replace memoize (callee, uses) u in
    (u, slice)

(* Transfer function when 'node' is a return node and 'p' is an exit node. *)
and transfer_ret global ctx dug node uses p (slice, visited, works) =
  let is_callee = not (is_list_empty ctx) in
  let caller = InterCfg.Node.get_pid node in
  let callee = InterCfg.Node.get_pid p in
  let _ =
    Printf.printf "From %s (%s), trace into %s() for uses = %s, ctx = %s\n"
      (node_to_lstr global node) caller callee (PowLoc.to_string uses)
      ("[" ^ String.concat " --> " (List.rev ctx) ^ "]")
  in
  let ctx = InterCfg.Node.get_pid node :: ctx in
  let use_at_entry, slice = find_callee_use global dug ctx uses p slice in
  let _ =
    Printf.printf "Traced function %s used %s to define %s\n" callee
      (PowLoc.to_string use_at_entry)
      (PowLoc.to_string uses)
  in
  let call_node = InterCfg.callof node global.icfg in
  let call_du = eval_def_use global global.mem call_node in
  let forward = PowLoc.diff use_at_entry call_du.defs in
  let defined = PowLoc.inter use_at_entry call_du.defs in
  let used = DefUseInfo.lookup_defs defined call_du in
  let slice =
    if is_callee then
      if PowLoc.is_empty defined then slice
      else SliceDFG.add_sliced_node call_node slice
    else (
      (* We will think that 'call_node' defines/forwards 'use_at_entry' to
       * 'node' (which is a return node), and 'node' defines 'uses' with it. *)
      SliceDFG.update_def_map node uses slice;
      SliceDFG.update_use_map node use_at_entry slice;
      SliceDFG.add_edge_owner node slice
      |> SliceDFG.draw_edge_fwd call_node node forward
      |> SliceDFG.draw_edge_def call_node node defined used)
  in
  let visited, works = update_works call_node forward used visited works in
  (slice, visited, works)

and transfer global dug ctx node uses (slice, visited, works) =
  let node_f = InterCfg.Node.get_pid node in
  let is_entry = InterCfg.is_entry node in
  let is_ret = InterCfg.is_returnnode node global.icfg in
  let preds = DUGraph.pred node dug in
  let folder p (slice, visited, works) =
    let p_f = InterCfg.Node.get_pid p in
    let locs_on_edge = DUGraph.get_abslocs p node dug in
    let uses = PowLoc.inter locs_on_edge uses in
    if PowLoc.is_empty uses then (slice, visited, works)
    else if is_entry && BatSet.mem (p_f, node_f) global.cyclic_calls then
      (slice, visited, works)
    else if is_ret && InterCfg.is_exit p then
      if BatSet.mem (node_f, p_f) global.cyclic_calls then
        skip_ret global node uses p (slice, visited, works)
      else
        transfer_normal global ctx node uses p (slice, visited, works)
    else transfer_normal global ctx node uses p (slice, visited, works)
  in
  list_fold folder preds (slice, visited, works)

(* Trace DUG until we reach the entry of 'callee'. Note that this does not mean
 * we trace intra-procedurally, since 'callee' can also call a function. *)
and trace_callee global dug ctx callee acc_uses slice visited works =
  match works with
  | [] -> (acc_uses, slice)
  | (node, uses) :: works when InterCfg.is_entry node ->
      let callee_check = InterCfg.Node.get_pid node in
      let _ = if callee <> callee_check then failwith "Unexpected" in
      let acc_uses = PowLoc.union uses acc_uses in
      trace_callee global dug ctx callee acc_uses slice visited works
  | (node, uses) :: works ->
      let slice, visited, works =
        transfer global dug ctx node uses (slice, visited, works)
      in
      trace_callee global dug ctx callee acc_uses slice visited works

let rec trace_trunk global dug slice visited works =
  match works with
  | [] -> slice
  | (node, uses) :: works ->
      let slice, visited, works =
        transfer global dug [] node uses (slice, visited, works)
      in
      trace_trunk global dug slice visited works

let print_to_file targ_id filename str_set =
  let slicing_dir = Filename.concat !Options.outdir targ_id in
  FileManager.mkdir slicing_dir;
  let oc = open_out (Filename.concat slicing_dir filename) in
  SS.iter (fun str -> output_string oc (str ^ "\n")) str_set;
  close_out oc

let dump_funcs global =
  let oc = open_out (Filename.concat !Options.outdir "func.txt") in
  let nodes = InterCfg.nodesof global.icfg in
  let folder n acc =
    if is_func_invalid global n then acc else SS.add (node_to_fstr global n) acc
  in
  let funcs = list_fold folder nodes SS.empty in
  SS.iter (fun s -> output_string oc (s ^ "\n")) funcs

let rec slice_control_deps global workset slice = 
  if NodeSet.is_empty workset then slice
  else
    let node, workset = NodeSet.pop workset in
    let slice = NodeSet.add node slice in
    let pid = Node.get_pid node in
    let node = Node.get_cfgnode node in
    let post_dom_fronts = InterCfg.cfgof global.icfg pid |> IntraCfg.post_dom_fronts node in
    let control_dep_nodes = 
      IntraCfg.NodeSet.fold 
        (fun n acc -> 
          let n = Node.make pid n in
          NodeSet.add n acc) post_dom_fronts NodeSet.empty
        in
    let workset = 
      NodeSet.fold 
        (fun n acc -> 
          if NodeSet.mem n slice then acc
          else NodeSet.add n acc) control_dep_nodes workset
        in
    let slice = NodeSet.union slice control_dep_nodes in
    slice_control_deps global workset slice

let perform_slicing global dug (targ_id, targ_line) =
  Printf.printf "Slicing for target '%s' begins\n%!" targ_id;
  Hashtbl.reset memoize;
  let t0 = Sys.time () in
  let targ_nodes = find_target_node_set global targ_line in
  let targ_func = find_target_func global targ_nodes in
  let slice, visited, works = initialize global targ_nodes in
  let slice = trace_trunk global dug slice visited works in
  Printf.printf "trace_trunk() finished\n%!";
  let slice_nodes = SliceDFG.get_sliced_nodes slice in
  (* We will always include the entry function (i.e. 'main') nodes, because AFL
   * requires at least one node is covered by the initial test cases. *)
  let entry_nodes = InterCfg.nodes_of_pid global.icfg !Options.entry_point in
  let nodes = NodeSet.union slice_nodes (NodeSet.of_list entry_nodes) in
  let folder n acc = SS.add (node_to_lstr global n) acc in
  let lines = NodeSet.fold folder nodes SS.empty in
  (* let control_dep_nodes = slice_control_deps global slice_nodes NodeSet.empty
  |> NodeSet.union (NodeSet.of_list entry_nodes) in
  let control_dep_lines = NodeSet.fold folder control_dep_nodes SS.empty in *)
  let folder n acc =
    if is_func_invalid global n then acc else SS.add (node_to_fstr global n) acc
  in
  let funcs = NodeSet.fold folder nodes SS.empty in
  let t1 = Sys.time () in
  Printf.printf "Enreting SliceDFG.get_du_edges()\n%!";
  let edges = SliceDFG.get_du_edges slice in
  let t2 = Sys.time () in
  let line_dfg = OutputDFG.init global targ_func targ_line edges in
  let t3 = Sys.time () in
  let dfg_nodes = OutputDFG.stringfy_nodes global line_dfg in
  let t4 = Sys.time () in
  L.info ~to_consol:true "Slicing for %s finished: %f sec\n" targ_id (t4 -. t0);
  L.info ~to_consol:true "DUG traversal time: %f sec\n" (t1 -. t0);
  L.info ~to_consol:true "Edge extraction time: %f sec\n" (t2 -. t1);
  L.info ~to_consol:true "Output DFG initialization time: %f sec\n" (t3 -. t2);
  L.info ~to_consol:true "Output DFG processing time: %f sec\n" (t4 -. t3);
  L.info ~to_consol:true "== Slicing report ==\n";
  L.info ~to_consol:true " - # DUG nodes  : %d\n" (DUGraph.nb_node dug);
  L.info ~to_consol:true " - # DUG edges  : %d\n" (DUGraph.nb_edge dug);
  L.info ~to_consol:true " - # DUG locs   : %d\n" (DUGraph.nb_loc dug);
  L.info ~to_consol:true " - # Sliced nodes : %d\n" (NodeSet.cardinal nodes);
  L.info ~to_consol:true " - # Sliced lines : %d\n" (SS.cardinal lines);
  (* L.info ~to_consol:true " - # Sliced control-dependent lines : %d\n" (SS.cardinal control_dep_lines); *)
  L.info ~to_consol:true " - # Sliced functions : %d\n" (SS.cardinal funcs);
  L.info ~to_consol:true " - # Output DFG nodes : %d\n" (SS.cardinal dfg_nodes);
  print_to_file targ_id "slice_line.txt" lines;
  print_to_file targ_id "slice_func.txt" funcs;
  print_to_file targ_id "slice_dfg.txt" dfg_nodes
  (* print_to_file targ_id "slice_control_dep_line.txt" control_dep_lines *)

let run global =
  let slicing_targets = BatMap.bindings !Options.slice_target_map in
  let dug = construct_dug global slicing_targets in
  List.iter (perform_slicing global dug) slicing_targets;
  L.info "Total elapsed time: ";
  print_elapsed_time ~level:0