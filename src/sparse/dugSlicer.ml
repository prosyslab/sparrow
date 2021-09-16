module Analysis = SparseAnalysis.Make (ItvSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module DUGraph = Analysis.DUGraph
module Node = InterCfg.Node
module PowNode = InterCfg.NodeSet

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

let rec compute_slice dug workset slice =
  if PowNode.is_empty workset then slice
  else
    let node, workset = PowNode.pop workset in
    let workset, slice =
      DUGraph.fold_pred
        (fun p (workset, slice) ->
          if PowNode.mem p slice then (workset, slice)
          else (PowNode.add p workset, PowNode.add p slice))
        dug node (workset, slice)
    in
    compute_slice dug workset slice

let run global dug =
  let target_node = find_target_node global dug in
  let t0 = Sys.time () in
  Logging.info ~to_consol:true "Slicing begins\n";
  let slice = compute_slice dug (PowNode.singleton target_node) PowNode.empty in
  let t1 = Sys.time () in
  Logging.info ~to_consol:true "Slicing completes: %f sec\n" (t1 -. t0);
  Logging.info ~to_consol:true "== Slicing report ==\n";
  Logging.info ~to_consol:true " - # Total nodes  : %d\n" (DUGraph.nb_node dug);
  Logging.info ~to_consol:true " - # Total edges  : %d\n" (DUGraph.nb_edge dug);
  Logging.info ~to_consol:true " - # Sliced nodes : %d\n"
    (PowNode.cardinal slice);
  let oc = open_out (Filename.concat !Options.outdir "slice.txt") in
  PowNode.iter
    (fun node ->
      let loc = string_of_node global node in
      output_string oc (loc ^ "\n"))
    slice;
  close_out oc;
  exit 0
