open BasicDom
open Vocab
module F = Format
module L = Logging
module Analysis = SparseAnalysis.Make (ItvSem)
module G = Analysis.DUGraph

let rec fix next reachable works g =
  if PowNode.is_empty works then reachable
  else
    let node, works = PowNode.pop works in
    let succs = next node g in
    let reachable, works =
      List.fold_left
        (fun (reachable, works) p ->
          if PowNode.mem p reachable then (reachable, works)
          else (PowNode.add p reachable, PowNode.add p works))
        (reachable, works) succs
    in
    fix next reachable works g

let optimize_reachability alarms g =
  let node_set =
    List.fold_left
      (fun set alarm -> PowNode.add alarm.Report.node set)
      PowNode.empty alarms
  in
  let src_set =
    List.fold_left
      (fun set alarm ->
        match alarm.Report.src with
        | Some (src, _) -> PowNode.add src set
        | _ -> set)
      PowNode.empty alarms
  in
  let reachable_from_node = fix G.pred node_set node_set g in
  let reachable_from_src = fix G.succ src_set src_set g in
  G.fold_node
    (fun n g ->
      if PowNode.mem n reachable_from_src && PowNode.mem n reachable_from_node
      then g
      else G.remove_node n g)
    g g

let optimize_inter_edge global old_g =
  G.fold_edges_e
    (fun src dst locset new_g ->
      if
        (not (InterCfg.is_callnode src global.Global.icfg))
        && (not (InterCfg.is_callnode dst global.Global.icfg))
        && (not (InterCfg.is_exit src))
        && not (InterCfg.is_exit dst)
      then G.add_abslocs src locset dst new_g
      else if
        InterCfg.is_callnode src global.Global.icfg && InterCfg.is_entry dst
      then new_g
      else new_g)
    old_g (G.create ())

module ReachingDef = BatSet.Make (struct
  type t = Node.t * G.Loc.t [@@deriving compare]
end)

let reachability2 global alarms g =
  let access = G.access g in
  let rec fix works results g =
    if ReachingDef.is_empty works then results
    else
      let ((node, use) as w), works = ReachingDef.pop works in
      G.fold_pred
        (fun p (works, results) ->
          let locs_on_edge = G.get_abslocs p node g in
          if G.PowLoc.mem use locs_on_edge then
            if ReachingDef.mem (p, use) results then (works, results)
            else
              let access = G.Access.find_node p access in
              let defs_pred = G.Access.Info.defof access in
              if G.PowLoc.mem use defs_pred then
                let uses_pred = G.Access.Info.useof access in
                ( G.PowLoc.fold (fun u -> ReachingDef.add (p, u)) uses_pred works,
                  ReachingDef.add (p, use) results )
              else
                ( ReachingDef.add (p, use) works,
                  ReachingDef.add (p, use) results )
          else if p = InterCfg.start_node then
            (works, ReachingDef.add (p, use) results)
          else (works, results))
        g node (works, results)
      |> fun (works, results) -> fix works results g
  in
  let works =
    List.fold_left
      (fun set alarm ->
        let node = alarm.Report.node in
        let access_node = G.Access.find_node node access in
        let uses = G.Access.Info.useof access_node in
        G.PowLoc.fold (fun x -> ReachingDef.add (node, x)) uses set)
      ReachingDef.empty alarms
  in
  let reachable_from_node = fix works works g in
  let reachable_from_node =
    ReachingDef.fold
      (fun x -> PowNode.add (fst x))
      reachable_from_node PowNode.empty
  in
  G.fold_node
    (fun n g ->
      if PowNode.mem n reachable_from_node then g else G.remove_node n g)
    g g

let optimize global alarms g =
  L.info "%d nodes and %d edges before optimization\n" (G.nb_node g)
    (G.nb_edge g);
  let g = optimize_reachability alarms g in
  L.info "%d nodes and %d edges after reachability\n" (G.nb_node g)
    (G.nb_edge g);
  let g = reachability2 global alarms g in
  L.info "%d nodes and %d edges after reachability2\n" (G.nb_node g)
    (G.nb_edge g);
  (*   let g = optimize_inter_edge global g in *)
  g

let print analysis global dug alarms =
  let dug = G.copy dug in
  let alarms = Report.get alarms Report.UnProven in
  let dug = optimize global alarms dug in
  let true_branch, false_branch =
    InterCfg.fold_cfgs
      (fun pid cfg (true_branch, false_branch) ->
        IntraCfg.fold_node
          (fun node (true_branch, false_branch) ->
            let succs = IntraCfg.succ node cfg in
            if List.length succs = 2 then
              ( PowNode.add
                  (InterCfg.Node.make pid (List.nth succs 1))
                  true_branch,
                PowNode.add
                  (InterCfg.Node.make pid (List.nth succs 0))
                  false_branch )
            else (true_branch, false_branch))
          cfg
          (true_branch, false_branch))
      global.Global.icfg
      (PowNode.empty, PowNode.empty)
  in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  let oc_edge = open_out (dirname ^ "/DUEdge.facts") in
  let oc_tc = open_out (dirname ^ "/TrueCond.facts") in
  let oc_tb = open_out (dirname ^ "/TrueBranch.facts") in
  let oc_fc = open_out (dirname ^ "/FalseCond.facts") in
  let oc_fb = open_out (dirname ^ "/FalseBranch.facts") in
  let fmt_edge = Format.formatter_of_out_channel oc_edge in
  let fmt_tc = Format.formatter_of_out_channel oc_tc in
  let fmt_tb = Format.formatter_of_out_channel oc_tb in
  let fmt_fc = Format.formatter_of_out_channel oc_fc in
  let fmt_fb = Format.formatter_of_out_channel oc_fb in
  G.iter_edges
    (fun src dst ->
      if PowNode.mem dst true_branch then (
        F.fprintf fmt_tc "%a\n" Node.pp src;
        F.fprintf fmt_tb "%a\t%a\n" Node.pp src Node.pp dst )
      else if PowNode.mem dst false_branch then (
        F.fprintf fmt_fc "%a\n" Node.pp src;
        F.fprintf fmt_fb "%a\t%a\n" Node.pp src Node.pp dst )
      else F.fprintf fmt_edge "%a\t%a\n" Node.pp src Node.pp dst)
    dug;
  close_out oc_edge;
  close_out oc_tc;
  close_out oc_tb;
  close_out oc_fc;
  close_out oc_fb

module AlarmSet = Set.Make (struct
  type t = Node.t * Node.t [@@deriving compare]
end)

let print_alarm analysis alarms =
  let alarms = Report.get alarms Report.UnProven in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  let oc = open_out (dirname ^ "/Alarm.facts") in
  let fmt = F.formatter_of_out_channel oc in
  ignore
    (List.fold_left
       (fun set alarm ->
         match alarm.Report.src with
         | Some (src_node, _) when not (AlarmSet.mem (src_node, alarm.node) set)
           ->
             F.fprintf fmt "%a\t%a\n" Node.pp src_node Node.pp alarm.node;
             AlarmSet.add (src_node, alarm.node) set
         | _ -> set)
       AlarmSet.empty alarms);
  F.pp_print_flush fmt ();
  close_out oc
