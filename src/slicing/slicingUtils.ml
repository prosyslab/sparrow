open Global
module SS = Set.Make (String)
module PowLoc = BasicDom.PowLoc
module Node = InterCfg.Node
module NodeSet = InterCfg.NodeSet

module EdgeSet = BatSet.Make (struct
  type t = Node.t * Node.t [@@deriving compare]
end)

module VisitLog = struct
  include BatMap.Make (Node)

  let update node locs visit_log =
    if mem node visit_log then
      let handled_locs = find node visit_log in
      let new_locs = PowLoc.diff locs handled_locs in
      (add node (PowLoc.union new_locs handled_locs) visit_log, new_locs)
    else (add node locs visit_log, locs)
end

let get_node_loc global node =
  InterCfg.cmdof global.icfg node |> IntraCfg.Cmd.location_of

let node_to_cmd global node =
  InterCfg.cmdof global.icfg node |> IntraCfg.Cmd.to_string

let node_to_filename global node =
  get_node_loc global node |> CilHelper.get_loc_filename

let node_to_lstr_abs global node =
  get_node_loc global node |> CilHelper.s_location_abs

let node_to_lstr global node = get_node_loc global node |> CilHelper.s_location

let node_to_lstr_verbose global node =
  let line_str = node_to_lstr global node in
  let node_str = Node.to_string node in
  let cmd_str = node_to_cmd global node in
  line_str ^ "(" ^ node_str ^ ") = " ^ cmd_str

let node_to_funcname global node =
  BatMap.find (node_to_lstr global node) global.line_to_func
  |> Str.split (Str.regexp "___[0-9]+")
  |> List.hd

let is_func_invalid global node =
  (* XXX. Strangely, some line string is not recorded in global.line_to_func *)
  node_to_filename global node = ""
  || (not (BatMap.mem (node_to_lstr global node) global.line_to_func))
  || node_to_funcname global node = InterCfg.global_proc

let node_to_fstr global node =
  node_to_filename global node ^ ":" ^ node_to_funcname global node

let find_target_func global targ_nodes =
  node_to_funcname global (NodeSet.min_elt targ_nodes)

let find_target_node_set global targ_str =
  let target_node_set =
    List.fold_left
      (fun target_set node ->
        let line =
          if String.contains targ_str '/' then node_to_lstr_abs global node
          else node_to_lstr global node
        in
        if line = targ_str then NodeSet.add node target_set else target_set)
      NodeSet.empty
      (InterCfg.nodesof global.icfg)
  in
  if NodeSet.is_empty target_node_set then failwith "Error: target not found";
  target_node_set

let target_nodes = ref NodeSet.empty

let register_target global targ_str =
  let targ_node_set = find_target_node_set global targ_str in
  target_nodes := NodeSet.union targ_node_set !target_nodes

let get_target_nodes () = !target_nodes