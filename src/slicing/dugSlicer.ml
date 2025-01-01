open Vocab
module L = Logging
module Val = ItvDom.Val
module Loc = BasicDom.Loc
module Node = InterCfg.Node
module NodeSet = InterCfg.NodeSet
module PowLoc = BasicDom.PowLoc
module SS = Set.Make (String)
module AccessAnalysis = AccessAnalysis.Make (SlicingSem.S)
module Access = AccessAnalysis.Access
module DUGraph = Dug.Make (Access)
module SsaDug = SsaDug.Make (DUGraph)
module EdgeSet = Slice.EdgeSet

module VisitMap = struct
  include BatMap.Make (Node)

  let update node locs visit_log =
    if mem node visit_log then
      let handled_locs = find node visit_log in
      let new_locs = PowLoc.diff locs handled_locs in
      (add node (PowLoc.union new_locs handled_locs) visit_log, new_locs)
    else (add node locs visit_log, locs)
end

let construct_dug global slicing_targets =
  let iterator (_, targ_str) = SlicingSem.register_target global targ_str in
  List.iter iterator slicing_targets;
  let locset = ItvAnalysis.get_locset global.Global.mem in
  (* We do not use semantics function to compute DU *)
  let dummy_sem _ (mem, global) = (mem, global) in
  let f_access = AccessAnalysis.perform global locset dummy_sem in
  let access =
    StepManager.stepf false "Access Analysis" f_access global.Global.mem
  in
  let init = (global, access, locset) in
  let dug = StepManager.stepf false "DUG construction" SsaDug.make init in
  prerr_memory_usage ();
  dug

let initialize global targ_nodes targ_line =
  let slice = Slice.init targ_nodes targ_line in
  let folder n (acc_visited, acc_works) =
    let uses = SlicingSem.eval_use_of_targ global global.Global.mem n in
    Slice.update_use_map n uses slice;
    (VisitMap.add n uses acc_visited, (n, uses) :: acc_works)
  in
  let visited, works = NodeSet.fold folder targ_nodes (VisitMap.empty, []) in
  (slice, visited, works)

let update_works node forward used visited works =
  let visited, new_fwds = VisitMap.update node forward visited in
  let visited, new_uses = VisitMap.update node used visited in
  let has_fwd = not (PowLoc.is_empty new_fwds) in
  let has_use = not (PowLoc.is_empty new_uses) in
  let works = if has_fwd then (node, new_fwds) :: works else works in
  let works = if has_use then (node, new_uses) :: works else works in
  (visited, works)

let transfer_normal global node uses p (slice, visited, works) =
  let node_f = InterCfg.Node.get_pid node in
  let p_f = InterCfg.Node.get_pid p in
  let _ =
    if node_f <> p_f then
      Printf.printf "Function changes: p_f = %s node_f = %s, uses = %s\n" p_f
        node_f (PowLoc.to_string uses)
  in
  let pred_du = SlicingSem.eval_def_use global global.Global.mem p in
  let forward = PowLoc.diff uses pred_du.defs in
  let defined = PowLoc.inter uses pred_du.defs in
  let used = SlicingSem.DefUseInfo.lookup_defs defined pred_du in
  let slice =
    Slice.draw_edge_fwd p node forward slice
    |> Slice.draw_edge_def p node defined used
  in
  let visited, works = update_works p forward used visited works in
  (slice, visited, works)

let skip_ret global node uses p (slice, visited, works) =
  let caller = InterCfg.Node.get_pid node in
  let callee = InterCfg.Node.get_pid p in
  let _ =
    Printf.printf "From %s (%s), ignore return from %s()\n"
      (InterCfg.node_to_lstr global.Global.icfg node)
      caller callee
  in
  let call_node = InterCfg.callof node global.Global.icfg in
  let slice = Slice.draw_edge_fwd call_node node uses slice in
  let visited, works = update_works call_node uses PowLoc.empty visited works in
  (slice, visited, works)

let transfer global dug node uses (slice, visited, works) =
  let node_f = InterCfg.Node.get_pid node in
  let is_entry = InterCfg.is_entry node in
  let is_ret = InterCfg.is_returnnode node global.Global.icfg in
  let preds = DUGraph.pred node dug in
  let folder p (slice, visited, works) =
    let p_f = InterCfg.Node.get_pid p in
    let locs_on_edge = DUGraph.get_abslocs p node dug in
    let uses = PowLoc.inter locs_on_edge uses in
    if PowLoc.is_empty uses then (slice, visited, works)
    else if is_entry && BatSet.mem (p_f, node_f) global.Global.cyclic_calls then
      (slice, visited, works)
    else if is_ret && InterCfg.is_exit p then
      if BatSet.mem (node_f, p_f) global.Global.cyclic_calls then
        skip_ret global node uses p (slice, visited, works)
      else transfer_normal global node uses p (slice, visited, works)
    else transfer_normal global node uses p (slice, visited, works)
  in
  list_fold folder preds (slice, visited, works)

let rec trace_trunk global dug slice visited works =
  match works with
  | [] -> slice
  | (node, uses) :: works ->
      let slice, visited, works =
        transfer global dug node uses (slice, visited, works)
      in
      trace_trunk global dug slice visited works

(* Identify the actual def nodes and foward nodes in the dugraph.
 * A forward node does not actually define the corresponding variable but passes it forward (e.g., PHI) *)
let rec slice_node global dug (slice, visited, works) =
  match works with
  | [] -> slice
  | (node, uses) :: works ->
      transfer global dug node uses (slice, visited, works)
      |> slice_node global dug

module WorkList = struct
  module M = BatMap.Make (Node)

  type t = PowLoc.t M.t

  let pop wl =
    if M.is_empty wl then None
    else
      let node, locs = M.min_binding wl in
      let wl = M.remove node wl in
      Some (node, locs, wl)

  let push node locs wl = M.modify_def PowLoc.empty node (PowLoc.union locs) wl
  let empty = M.empty
end

(* Find def-use edges toward the user node 'dst_node' *)
let rec get_du_edges_to dst_node dfg edges visited wl =
  match WorkList.pop wl with
  | None -> edges
  | Some (node, uses, wl) ->
      let pred_entries = Slice.get_pred_entries node dfg in
      let folder (edges, visited, works) (p, locs_on_edge) =
        let passed_uses = PowLoc.inter locs_on_edge uses in
        if PowLoc.is_empty passed_uses then (edges, visited, works)
        else
          let defs = Slice.lookup_def_map p dfg in
          let fwds = Slice.lookup_fwd_map p dfg in
          let defined_uses = PowLoc.inter passed_uses defs in
          let forward_uses = PowLoc.inter passed_uses fwds in
          let edges =
            if PowLoc.is_empty defined_uses then edges
            else EdgeSet.add (p, dst_node) edges
          in
          let visited, new_uses = VisitMap.update p forward_uses visited in
          if PowLoc.is_empty new_uses then (edges, visited, works)
          else (edges, visited, WorkList.push p new_uses works)
      in
      let edges, visited, wl =
        List.fold_left folder (edges, visited, wl) pred_entries
      in
      get_du_edges_to dst_node dfg edges visited wl

(* Identify actual def-use edges for each sliced node *)
let slice_edge dfg =
  let folder n acc =
    let uses = Slice.lookup_use_map n dfg in
    let visited = VisitMap.add n uses VisitMap.empty in
    let wl = WorkList.push n uses WorkList.empty in
    let edges = get_du_edges_to n dfg EdgeSet.empty visited wl in
    EdgeSet.union edges acc
  in
  let sliced_edges = NodeSet.fold folder dfg.sliced_nodes EdgeSet.empty in
  { dfg with sliced_edges }

let rec slice_control_nodes_internal global works sliced_control_nodes =
  if BatSet.is_empty works then sliced_control_nodes
  else
    let icfg = global.Global.icfg in
    let (k, node), works = BatSet.pop works in
    let post_dom_fronts = InterCfg.get_post_dom_fronts node icfg in
    let control_nodes = NodeSet.diff post_dom_fronts sliced_control_nodes in
    (* Add call nodes to the worklist when we reach the end of intra-procedural control dependency *)
    let call_nodes =
      if NodeSet.is_empty control_nodes then
        let callers = Node.get_pid node |> InterCfg.get_callers icfg in
        NodeSet.diff callers sliced_control_nodes
      else NodeSet.empty
    in
    let works =
      if !Options.max_control_deps == 0 || k < !Options.max_control_deps then
        works
        |> NodeSet.fold (fun n acc -> BatSet.add (k + 1, n) acc) control_nodes
        (* k is same here because call nodes are skipped and do not increase the k *)
        |> NodeSet.fold (fun n acc -> BatSet.add (k, n) acc) call_nodes
      else works
    in
    slice_control_nodes_internal global works
      (NodeSet.add node sliced_control_nodes)

let slice_control_nodes global slice =
  let _, targ_line = slice.Slice.target in
  let targ_nodes = InterCfg.nodes_of_line global.Global.icfg targ_line in
  let works =
    NodeSet.fold (fun n acc -> BatSet.add (0, n) acc) targ_nodes BatSet.empty
  in
  let sliced_nodes = slice_control_nodes_internal global works NodeSet.empty in
  (* sliced_call_nodes are targets of semantic coverage
     sliced_control_nodes are targets of taint analysis *)
  let _, sliced_control_nodes =
    NodeSet.partition
      (fun n -> InterCfg.is_callnode n global.Global.icfg)
      sliced_nodes
  in
  { slice with sliced_control_nodes }

let perform_slicing global dug (targ_id, targ_line) =
  let targ_nodes = InterCfg.nodes_of_line global.Global.icfg targ_line in
  let targ_func =
    InterCfg.find_target_func global.Global.icfg global.Global.line_to_func
      targ_nodes
  in
  (targ_func, targ_line)
  |> StepManager.stepf false "Initialize" (initialize global targ_nodes)
  |> StepManager.stepf false "Node slicing" (slice_node global dug)
  |> StepManager.stepf false "Edge slicing" slice_edge
  |> StepManager.stepf false "Control nodes slicing"
       (slice_control_nodes global)
  |> StepManager.stepf false "Constructing sliced graph" (Slice.generate global)
  |> StepManager.stepf false "Print" (Slice.print global targ_id)

let to_json (global, dug) =
  `Assoc
    [
      ("callgraph", CallGraph.to_json global.Global.callgraph);
      ("cfgs", InterCfg.to_json global.Global.icfg);
      ("dugraph", DUGraph.to_json dug);
    ]

let print_dug global dug =
  let out_dir = !Options.outdir in
  let oc = open_out (Filename.concat out_dir "dug.json") in
  to_json (global, dug) |> Yojson.Safe.pretty_to_channel oc;
  close_out oc

let run global =
  let slicing_targets = BatMap.bindings !Options.slice_target_map in
  let dug = construct_dug global slicing_targets in
  if !Options.dug then print_dug global dug;
  let perform_slicing = perform_slicing global dug in
  List.iter
    (fun (targ_id, targ_line) ->
      StepManager.stepf true ("Slicing for " ^ targ_id) perform_slicing
        (targ_id, targ_line))
    slicing_targets;
  L.info "Total elapsed time: ";
  print_elapsed_time ~level:0
