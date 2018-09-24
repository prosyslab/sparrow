open BasicDom
open Vocab

module L = Logging
module Analysis = SparseAnalysis.Make(ItvSem)
module G = Analysis.DUGraph

let rec fix next reachable works g =
  if PowNode.is_empty works then reachable
  else
    let (node, works) = PowNode.pop works in
    let succs = next node g in
    let (reachable, works) =
      List.fold_left (fun (reachable, works) p ->
          if PowNode.mem p reachable then (reachable, works)
          else (PowNode.add p reachable, PowNode.add p works)) (reachable, works) succs
    in
    fix next reachable works g

let optimize_reachability alarms g =
  let node_set =
    List.fold_left (fun set alarm -> PowNode.add alarm.Report.node set)
      PowNode.empty alarms
  in
  let src_set =
    List.fold_left (fun set alarm ->
        match alarm.Report.src with
        | Some (src, _) -> PowNode.add src set
        | _ -> set) PowNode.empty alarms
  in
  let reachable_from_node = fix G.pred node_set node_set g in
  let reachable_from_src = fix G.succ src_set src_set g in
  G.fold_node (fun n g ->
      if PowNode.mem n reachable_from_src
      && PowNode.mem n reachable_from_node then g
      else G.remove_node n g) g g

let optimize_inter_edge g =
  g

let optimize global alarms g =
  L.info "%d nodes and %d edges before optimization\n" (G.nb_node g) (G.nb_edge g);
  let g = optimize_reachability alarms g in
  L.info "%d nodes and %d edges after reachability\n" (G.nb_node g) (G.nb_edge g);
  let g = optimize_inter_edge g in
  g

let print global dug alarms =
  let alarms = Report.get alarms Report.UnProven in
  let dug = optimize global alarms dug in
  let oc = open_out (!Options.outdir ^ "/datalog/DUEdge.facts") in
  let fmt = Format.formatter_of_out_channel oc in
  G.iter_edges_e (fun src dst locset ->
      if Node.equal src InterCfg.start_node && PowLoc.is_empty locset then
        Format.fprintf fmt "%a\tdummy\t%a\n" Node.pp src Node.pp dst
      else
        PowLoc.iter (fun l ->
            Format.fprintf fmt "%a\t%a\t%a\n" Node.pp src Loc.pp l Node.pp dst)
          locset) dug;
  close_out oc
