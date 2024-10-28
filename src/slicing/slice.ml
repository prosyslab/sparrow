module PowLoc = BasicDom.PowLoc
module Node = InterCfg.Node
module NodeSet = InterCfg.NodeSet
module SS = Set.Make (String)
module L = Logging

module Line = struct
  type t = string * string

  let compare = Stdlib.compare

  let equal = ( = )

  let hash = Hashtbl.hash
end

(* module Line = String *)
module LineLevelG = Graph.Imperative.Digraph.ConcreteBidirectional (Line)

module W = struct
  type edge = LineLevelG.E.t

  type t = int

  let weight _ = 1

  let compare = compare

  let add = ( + )

  let zero = 0
end

module Dijkstra = Graph.Path.Dijkstra (LineLevelG) (W)

type du_map = {
  succs : (Node.t, NodeSet.t) Hashtbl.t;
  preds : (Node.t, NodeSet.t) Hashtbl.t;
  labels : (Node.t * Node.t, PowLoc.t) Hashtbl.t;
  defs : (Node.t, PowLoc.t) Hashtbl.t;
  uses : (Node.t, PowLoc.t) Hashtbl.t;
  fwds : (Node.t, PowLoc.t) Hashtbl.t;
}

module Edge = struct
  type t = Node.t * Node.t [@@deriving compare]
end

module EdgeSet = BatSet.Make (Edge)

type t = {
  sliced_nodes : NodeSet.t;
  sliced_control_nodes : NodeSet.t;
  sliced_edges : EdgeSet.t;
  du_map : du_map;
  graph : LineLevelG.t;
  target : Line.t;
  output_nodes : SS.t;
}

let add_direct_edge global graph src_node dst_node =
  let icfg = global.Global.icfg in
  let line_to_func = global.Global.line_to_func in
  let src_func = InterCfg.node_to_filtered_pid icfg line_to_func src_node in
  let src_line = InterCfg.node_to_lstr icfg src_node in
  let src = (src_func, src_line) in
  let dst_func = InterCfg.node_to_filtered_pid icfg line_to_func dst_node in
  let dst_line = InterCfg.node_to_lstr icfg dst_node in
  let dst = (dst_func, dst_line) in
  if not (LineLevelG.V.equal src dst) then LineLevelG.add_edge graph src dst

let generate global slice =
  EdgeSet.iter
    (fun (src, dst) -> add_direct_edge global slice.graph src dst)
    slice.sliced_edges;
  slice

let rec list_max = function
  | [] -> failwith "empty list to list_max()"
  | [ x ] -> x
  | head :: tail ->
      let tail_max = list_max tail in
      if head > tail_max then head else tail_max

let init targ_nodes targ_line =
  let sliced_nodes = targ_nodes in
  let sliced_control_nodes = NodeSet.empty in
  let sliced_edges = EdgeSet.empty in
  let succs = Hashtbl.create 10000 in
  let preds = Hashtbl.create 10000 in
  let labels = Hashtbl.create 50000 in
  let defs = Hashtbl.create 10000 in
  let uses = Hashtbl.create 10000 in
  let fwds = Hashtbl.create 10000 in
  let du_map = { succs; preds; labels; defs; uses; fwds } in
  let graph = LineLevelG.create () in
  let target = targ_line in
  let output_nodes = SS.empty in
  {
    sliced_nodes;
    sliced_control_nodes;
    sliced_edges;
    du_map;
    graph;
    target;
    output_nodes;
  }

let get_preds node dfg =
  if Hashtbl.mem dfg.du_map.preds node then Hashtbl.find dfg.du_map.preds node
  else NodeSet.empty

let get_succs node dfg =
  if Hashtbl.mem dfg.du_map.succs node then Hashtbl.find dfg.du_map.succs node
  else NodeSet.empty

let get_label_locs src dst dfg =
  if Hashtbl.mem dfg.du_map.labels (src, dst) then
    Hashtbl.find dfg.du_map.labels (src, dst)
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
  if Hashtbl.mem dfg.du_map.succs src then
    let prev_succs = Hashtbl.find dfg.du_map.succs src in
    Hashtbl.replace dfg.du_map.succs src (NodeSet.add dst prev_succs)
  else Hashtbl.replace dfg.du_map.succs src (NodeSet.singleton dst)

let add_pred_edge src dst dfg =
  if Hashtbl.mem dfg.du_map.preds dst then
    let prev_preds = Hashtbl.find dfg.du_map.preds dst in
    Hashtbl.replace dfg.du_map.preds dst (NodeSet.add src prev_preds)
  else Hashtbl.replace dfg.du_map.preds dst (NodeSet.singleton src)

let add_edge src dst dfg =
  add_succ_edge src dst dfg;
  add_pred_edge src dst dfg

let add_label_locs src dst locs dfg =
  if Hashtbl.mem dfg.du_map.labels (src, dst) then
    let prev_locs = Hashtbl.find dfg.du_map.labels (src, dst) in
    let new_locs = PowLoc.union locs prev_locs in
    Hashtbl.replace dfg.du_map.labels (src, dst) new_locs
  else Hashtbl.replace dfg.du_map.labels (src, dst) locs

let update_loc_map node locs du_map =
  if Hashtbl.mem du_map node then
    let prev_locs = Hashtbl.find du_map node in
    Hashtbl.replace du_map node (PowLoc.union locs prev_locs)
  else Hashtbl.replace du_map node locs

let update_def_map node defs dfg = update_loc_map node defs dfg.du_map.defs

let update_use_map node uses dfg = update_loc_map node uses dfg.du_map.uses

let update_fwd_map node fwds dfg = update_loc_map node fwds dfg.du_map.fwds

let lookup_loc_map node du_map =
  if Hashtbl.mem du_map node then Hashtbl.find du_map node else PowLoc.empty

let lookup_def_map node dfg = lookup_loc_map node dfg.du_map.defs

let lookup_use_map node dfg = lookup_loc_map node dfg.du_map.uses

let lookup_fwd_map node dfg = lookup_loc_map node dfg.du_map.fwds

(* 'src' defines 'defined' by using 'used', and this def is passed to 'dst'. *)
let draw_edge_def src dst defined used dfg =
  if PowLoc.is_empty defined then dfg
  else
    let sliced_nodes = NodeSet.add src dfg.sliced_nodes in
    add_edge src dst dfg;
    add_label_locs src dst defined dfg;
    update_def_map src defined dfg;
    update_use_map src used dfg;
    { dfg with sliced_nodes }

(* 'src' simply forwards 'locs' to 'dst. *)
let draw_edge_fwd src dst locs dfg =
  if PowLoc.is_empty locs then dfg
  else (
    add_edge src dst dfg;
    add_label_locs src dst locs dfg;
    update_fwd_map src locs dfg;
    dfg)

let print_stat nodes lines control_nodes control_lines funcs =
  L.info ~to_consol:true "== Slicing report ==\n";
  L.info ~to_consol:true "%-16s: %d\n" "# Sliced nodes" (NodeSet.cardinal nodes);
  L.info ~to_consol:true "%-16s: %d\n" "# Sliced lines" (SS.cardinal lines);
  L.info ~to_consol:true "%-16s: %d\n" "# Sliced control nodes"
    (NodeSet.cardinal control_nodes);
  L.info ~to_consol:true "%-16s: %d\n" "# Sliced control lines"
    (SS.cardinal control_lines);
  L.info ~to_consol:true "%-16s: %d\n" "# Sliced functions" (SS.cardinal funcs)

let print_one_file targ_id file_name str_set =
  let slicing_dir = Filename.concat !Options.outdir "slice" in
  FileManager.mkdir slicing_dir;
  let target_dir = Filename.concat slicing_dir targ_id in
  FileManager.mkdir target_dir;
  let oc = open_out (Filename.concat target_dir file_name) in
  SS.iter (fun str -> output_string oc (str ^ "\n")) str_set;
  close_out oc

let print_to_files targ_id lines control_lines funcs relevance_score =
  print_one_file targ_id "slice_line.txt" lines;
  print_one_file targ_id "slice_control_line.txt" control_lines;
  print_one_file targ_id "slice_func.txt" funcs;
  print_one_file targ_id "slice_dfg.txt" relevance_score

let filter_slice_lines lines =
  let filter line =
    let parts = Str.split (Str.regexp ":") line in
    match parts with [ _; line_number ] -> line_number <> "0" | _ -> false
  in
  SS.filter filter lines

let compute_relevance_score global dfg =
  let pids = InterCfg.pidsof global.Global.icfg in
  let folder v acc_entries =
    let func, line = v in
    let dist = Dijkstra.shortest_path dfg.graph v dfg.target |> snd in
    if not (List.mem func pids) then acc_entries
    else (dist, line) :: acc_entries
  in
  let entries = LineLevelG.fold_vertex folder dfg.graph [] in
  let max_dist = List.map fst entries |> list_max in
  let folder acc_strs (dist, line) =
    SS.add (Printf.sprintf "%d %s" (max_dist - dist + 1) line) acc_strs
  in
  List.fold_left folder SS.empty entries

let print global targ_id dfg =
  let icfg = global.Global.icfg in
  let line_to_func = global.Global.line_to_func in
  (* We will always include the entry function (i.e. 'main') nodes. *)
  let entry_nodes = InterCfg.nodes_of_pid icfg !Options.entry_point in
  let nodes = NodeSet.union dfg.sliced_nodes (NodeSet.of_list entry_nodes) in
  let folder n acc = SS.add (InterCfg.node_to_lstr icfg n) acc in
  let lines =
    NodeSet.fold folder nodes SS.empty
    |> SS.remove "unknown" |> filter_slice_lines
  in
  let control_lines =
    NodeSet.fold folder dfg.sliced_control_nodes SS.empty
    |> SS.remove "unknown" |> filter_slice_lines
  in
  let folder n acc =
    if InterCfg.is_func_name_invalid icfg line_to_func n then acc
    else SS.add (InterCfg.node_to_fstr icfg line_to_func n) acc
  in
  let funcs = NodeSet.fold folder nodes SS.empty |> SS.remove "unknown" in
  let relevance_score = compute_relevance_score global dfg in
  print_stat dfg.sliced_nodes relevance_score dfg.sliced_control_nodes
    control_lines funcs;
  print_to_files targ_id lines control_lines funcs relevance_score
