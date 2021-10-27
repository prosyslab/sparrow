module Analysis = SparseAnalysis.Make (ItvSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module DUGraph = Analysis.DUGraph
module Node = InterCfg.Node
module PowNode = InterCfg.NodeSet
module SS = Set.Make (String)
module PowLoc = BasicDom.PowLoc
module Access = DUGraph.Access

module ReachDef = BatSet.Make (struct
  type t = Node.t * BasicDom.Loc.t [@@deriving compare]
end)

let location_of_node global node =
  InterCfg.cmdof global.Global.icfg node |> IntraCfg.Cmd.location_of

let string_of_node global node =
  let loc = location_of_node global node in
  loc.Cil.file ^ ":" ^ string_of_int loc.Cil.line

let find_target_node global dug =
  DUGraph.fold_node
    (fun node res ->
      if Option.is_none res then
        let loc = string_of_node global node in
        if loc = !Options.dug_slice_target then Some node else None
      else res)
    dug None
  |> function
  | Some n -> n
  | None ->
      prerr_endline "Error: target not found";
      exit 1

let find_target_node_set global dug =
  let target_node_set =
    DUGraph.fold_node
      (fun node target_set ->
        let loc = string_of_node global node in
        if loc = !Options.dug_slice_target then PowNode.add node target_set
        else target_set)
      dug PowNode.empty
  in
  if PowNode.is_empty target_node_set then (
    prerr_endline "Error: target not found";
    exit 1)
  else target_node_set

let rec compute_slice global dug workset slice =
  if ReachDef.is_empty workset then slice
  else
    let (node, use), workset = ReachDef.pop workset in
    let access = DUGraph.access dug in
    let workset, slice =
      DUGraph.fold_pred
        (fun p (workset, slice) ->
          let locs_on_edge = DUGraph.get_abslocs p node dug in
          if PowLoc.mem use locs_on_edge then
            if ReachDef.mem (p, use) slice then (workset, slice)
            else
              let access = Access.find_node p access in
              let defs_pred = Access.Info.defof access in
              if PowLoc.mem use defs_pred then
                let uses_pred = Access.Info.useof access in
                ( PowLoc.fold (fun u -> ReachDef.add (p, u)) uses_pred workset,
                  ReachDef.add (p, use) slice )
              else (ReachDef.add (p, use) workset, ReachDef.add (p, use) slice)
          else (workset, slice))
        dug node (workset, slice)
    in
    compute_slice global dug workset slice

let count_sliced_lines global slice =
  List.rev_map
    (fun node -> string_of_node global node)
    (List.rev (PowNode.elements slice))
  |> List.fold_left (fun line_set elem -> SS.add elem line_set) SS.empty
  |> SS.cardinal

let count_DUG_lines global dug =
  DUGraph.fold_node
    (fun node line_set ->
      let loc = string_of_node global node in
      SS.add loc line_set)
    dug SS.empty
  |> SS.cardinal

let print_sliced_lines global slice =
  let oc = open_out (Filename.concat !Options.outdir "slice_line.txt") in
  let line_list =
    List.rev_map
      (fun node -> string_of_node global node)
      (List.rev (PowNode.elements slice))
    |> List.fold_left (fun line_set elem -> SS.add elem line_set) SS.empty
    |> SS.elements
  in
  List.iter (fun str -> output_string oc (str ^ "\n")) line_list;
  close_out oc

let run global dug =
  let target_node_set = find_target_node_set global dug in
  let works =
    PowNode.fold
      (fun n works ->
        let locs =
          Access.find_node n (DUGraph.access dug) |> Access.Info.useof
        in
        PowLoc.fold (fun x -> ReachDef.add (n, x)) locs works)
      target_node_set ReachDef.empty
  in
  let t0 = Sys.time () in
  Logging.info ~to_consol:true "Slicing begins\n";
  let sliced_reaching_def = compute_slice global dug works works in
  let slice =
    ReachDef.fold
      (fun x -> PowNode.add (fst x))
      sliced_reaching_def PowNode.empty
  in
  let t1 = Sys.time () in
  Logging.info ~to_consol:true "Slicing completes: %f sec\n" (t1 -. t0);
  Logging.info ~to_consol:true "== Slicing report ==\n";
  Logging.info ~to_consol:true " - # Total nodes  : %d\n" (DUGraph.nb_node dug);
  Logging.info ~to_consol:true " - # Total edges  : %d\n" (DUGraph.nb_edge dug);
  Logging.info ~to_consol:true " - # Total lines  : %d\n"
    (count_DUG_lines global dug);
  Logging.info ~to_consol:true " - # Sliced nodes : %d\n"
    (PowNode.cardinal slice);
  Logging.info ~to_consol:true " - # Sliced lines : %d\n"
    (count_sliced_lines global slice);
  let oc = open_out (Filename.concat !Options.outdir "slice.txt") in
  PowNode.iter
    (fun node ->
      let loc = string_of_node global node in
      output_string oc (loc ^ "\n"))
    slice;
  close_out oc;
  print_sliced_lines global slice;
  exit 0
