open Vocab
open SlicingUtils

type t = {
  sliced_nodes : NodeSet.t;
  edge_owners : NodeSet.t;
  succs : (Node.t, NodeSet.t) Hashtbl.t;
  preds : (Node.t, NodeSet.t) Hashtbl.t;
  labels : (Node.t * Node.t, PowLoc.t) Hashtbl.t;
  defs : (Node.t, PowLoc.t) Hashtbl.t;
  uses : (Node.t, PowLoc.t) Hashtbl.t;
  fwds : (Node.t, PowLoc.t) Hashtbl.t;
}

let init targ_nodes =
  let sliced_nodes = targ_nodes in
  let edge_owners = targ_nodes in
  let succs = Hashtbl.create 10000 in
  let preds = Hashtbl.create 10000 in
  let labels = Hashtbl.create 50000 in
  let defs = Hashtbl.create 10000 in
  let uses = Hashtbl.create 10000 in
  let fwds = Hashtbl.create 10000 in
  { sliced_nodes; edge_owners; succs; preds; labels; defs; uses; fwds }

let get_preds node dfg =
  if Hashtbl.mem dfg.preds node then Hashtbl.find dfg.preds node
  else NodeSet.empty

let get_succs node dfg =
  if Hashtbl.mem dfg.succs node then Hashtbl.find dfg.succs node
  else NodeSet.empty

let get_label_locs src dst dfg =
  if Hashtbl.mem dfg.labels (src, dst) then Hashtbl.find dfg.labels (src, dst)
  else PowLoc.empty

(* Return predecessors along with the locs labelled on that edge *)
let get_pred_entries node dfg =
  let preds = get_preds node dfg in
  let folder p acc = (p, get_label_locs p node dfg) :: acc in
  NodeSet.fold folder preds []

(* Return successors along with the locs labelled on that edge *)
let get_succ_entries node dfg =
  let succs = get_succs node dfg in
  let folder s acc = (s, get_label_locs node s dfg) :: acc in
  NodeSet.fold folder succs []

let add_succ_edge src dst dfg =
  if Hashtbl.mem dfg.succs src then
    let prev_succs = Hashtbl.find dfg.succs src in
    Hashtbl.replace dfg.succs src (NodeSet.add dst prev_succs)
  else Hashtbl.replace dfg.succs src (NodeSet.singleton dst)

let add_pred_edge src dst dfg =
  if Hashtbl.mem dfg.preds dst then
    let prev_preds = Hashtbl.find dfg.preds dst in
    Hashtbl.replace dfg.preds dst (NodeSet.add src prev_preds)
  else Hashtbl.replace dfg.preds dst (NodeSet.singleton src)

let add_edge src dst dfg =
  add_succ_edge src dst dfg;
  add_pred_edge src dst dfg

let add_label_locs src dst locs dfg =
  if Hashtbl.mem dfg.labels (src, dst) then
    let prev_locs = Hashtbl.find dfg.labels (src, dst) in
    let new_locs = PowLoc.union locs prev_locs in
    Hashtbl.replace dfg.labels (src, dst) new_locs
  else Hashtbl.replace dfg.labels (src, dst) locs

let update_loc_map node locs du_map =
  if Hashtbl.mem du_map node then
    let prev_locs = Hashtbl.find du_map node in
    Hashtbl.replace du_map node (PowLoc.union locs prev_locs)
  else Hashtbl.replace du_map node locs

let update_def_map node defs dfg = update_loc_map node defs dfg.defs

let update_use_map node uses dfg = update_loc_map node uses dfg.uses

let update_fwd_map node fwds dfg = update_loc_map node fwds dfg.fwds

let lookup_loc_map node du_map =
  if Hashtbl.mem du_map node then Hashtbl.find du_map node else PowLoc.empty

let lookup_def_map node dfg = lookup_loc_map node dfg.defs

let lookup_use_map node dfg = lookup_loc_map node dfg.uses

let lookup_fwd_map node dfg = lookup_loc_map node dfg.fwds

(* 'src' defines 'defined' by using 'used', and this def is passed to 'dst'. *)
let draw_edge_def src dst defined used dfg =
  if PowLoc.is_empty defined then dfg
  else
    let sliced_nodes = NodeSet.add src dfg.sliced_nodes in
    let edge_owners = NodeSet.add src dfg.edge_owners in
    add_edge src dst dfg;
    add_label_locs src dst defined dfg;
    update_def_map src defined dfg;
    update_use_map src used dfg;
    { dfg with sliced_nodes; edge_owners }

(* 'src' simply forwards 'locs' to 'dst. *)
let draw_edge_fwd src dst locs dfg =
  if PowLoc.is_empty locs then dfg
  else (
    add_edge src dst dfg;
    add_label_locs src dst locs dfg;
    update_fwd_map src locs dfg;
    dfg)

let add_sliced_node n dfg =
  { dfg with sliced_nodes = NodeSet.add n dfg.sliced_nodes }

let add_edge_owner n dfg =
  { dfg with edge_owners = NodeSet.add n dfg.edge_owners }

let get_sliced_nodes dfg = dfg.sliced_nodes

(* Find def-use edges toward the user node 'dst_node' *)
let rec get_du_edges_to dst_node dfg edges visited = function
  | [] -> edges
  | (node, uses) :: works ->
      let pred_entries = get_pred_entries node dfg in
      let folder (p, locs_on_edge) (edges, visited, works) =
        let passed_uses = PowLoc.inter locs_on_edge uses in
        if PowLoc.is_empty passed_uses then (edges, visited, works)
        else
          let defs = lookup_def_map p dfg in
          let fwds = lookup_fwd_map p dfg in
          let defined_uses = PowLoc.inter passed_uses defs in
          let forward_uses = PowLoc.inter passed_uses fwds in
          let edges =
            if PowLoc.is_empty defined_uses then edges
            else EdgeSet.add (p, dst_node) edges
          in
          let visited, new_uses = VisitLog.update p forward_uses visited in
          if PowLoc.is_empty new_uses then (edges, visited, works)
          else (edges, visited, (p, new_uses) :: works)
      in
      let edges, visited, works =
        list_fold folder pred_entries (edges, visited, works)
      in
      get_du_edges_to dst_node dfg edges visited works

let get_du_edges dfg =
  let folder n acc =
    let uses = lookup_use_map n dfg in
    let visited = VisitLog.add n uses VisitLog.empty in
    let edges = get_du_edges_to n dfg EdgeSet.empty visited [ (n, uses) ] in
    EdgeSet.union edges acc
  in
  NodeSet.fold folder dfg.edge_owners EdgeSet.empty
