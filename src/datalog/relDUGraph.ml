open BasicDom
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

let reachability2 alarms g =
  let access = G.access g in
  let rec fix works results g =
    if ReachingDef.is_empty works then results
    else
      let (node, use), works = ReachingDef.pop works in
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

let optimize alarms g =
  L.info "%d nodes and %d edges before optimization\n" (G.nb_node g)
    (G.nb_edge g);
  let g = optimize_reachability alarms g in
  L.info "%d nodes and %d edges after reachability\n" (G.nb_node g)
    (G.nb_edge g);
  let g = reachability2 alarms g in
  L.info "%d nodes and %d edges after reachability2\n" (G.nb_node g)
    (G.nb_edge g);
  (*   let g = optimize_inter_edge global g in *)
  g

let print analysis global dug alarms =
  let dug = G.copy dug in
  let alarms = Report.get alarms Report.UnProven in
  let dug = optimize alarms dug in
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
  let oc_loophead = open_out (dirname ^ "/LoopHead.facts") in
  let fmt_edge = Format.formatter_of_out_channel oc_edge in
  let fmt_tc = Format.formatter_of_out_channel oc_tc in
  let fmt_tb = Format.formatter_of_out_channel oc_tb in
  let fmt_fc = Format.formatter_of_out_channel oc_fc in
  let fmt_fb = Format.formatter_of_out_channel oc_fb in
  let fmt_loophead = Format.formatter_of_out_channel oc_loophead in
  G.iter_edges
    (fun src dst ->
      if BatSet.mem dst (G.loopheads dug) then
        F.fprintf fmt_loophead "%a\n" Node.pp dst;
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

type formatter = {
  alarm : F.formatter;
  array_exp : F.formatter;
  deref_exp : F.formatter;
  div_exp : F.formatter;
  strcpy : F.formatter;
  strncpy : F.formatter;
  strcat : F.formatter;
  taint : F.formatter;
}

let alarm_count = ref 0

let alarm_exp_map = Hashtbl.create 1000

let new_alarm_exp_id aexp =
  let id = "Alarm-" ^ string_of_int !alarm_count in
  alarm_count := !alarm_count + 1;
  Hashtbl.add alarm_exp_map aexp id;
  id

let find_lv lv_map l =
  try Hashtbl.find lv_map l with _ -> "UnknownLv-" ^ CilHelper.s_lv l

let find_exp exp_map e =
  try Hashtbl.find exp_map e with _ -> "UnknownExp-" ^ CilHelper.s_exp e

let pp_alarm_exp fmt aexp =
  let id = new_alarm_exp_id aexp in
  match aexp with
  | AlarmExp.ArrayExp (l, e, _) ->
      let l_id = find_lv RelSyntax.lv_map l in
      let e_id = find_exp RelSyntax.exp_map e in
      F.fprintf fmt.array_exp "%s\t%s\t%s\n" id l_id e_id
  | DerefExp (e, _) ->
      let e_id = find_exp RelSyntax.exp_map e in
      F.fprintf fmt.deref_exp "%s\t%s\n" id e_id
  | DivExp (e1, e2, _) ->
      let e1_id, e2_id =
        (find_exp RelSyntax.exp_map e1, find_exp RelSyntax.exp_map e2)
      in
      F.fprintf fmt.div_exp "%s\t%s\t%s\n" id e1_id e2_id
  | Strcpy (e1, e2, _) ->
      let e1_id, e2_id =
        (find_exp RelSyntax.exp_map e1, find_exp RelSyntax.exp_map e2)
      in
      F.fprintf fmt.strcpy "%s\t%s\t%s\n" id e1_id e2_id
  | Strcat (e1, e2, _) ->
      let e1_id, e2_id =
        (find_exp RelSyntax.exp_map e1, find_exp RelSyntax.exp_map e2)
      in
      F.fprintf fmt.strcat "%s\t%s\t%s\n" id e1_id e2_id
  | Strncpy (e1, e2, e3, _) ->
      let e1_id, e2_id, e3_id =
        ( find_exp RelSyntax.exp_map e1,
          find_exp RelSyntax.exp_map e2,
          find_exp RelSyntax.exp_map e3 )
      in
      F.fprintf fmt.strncpy "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | Memcpy (e1, e2, e3, _) ->
      let e1_id, e2_id, e3_id =
        ( find_exp RelSyntax.exp_map e1,
          find_exp RelSyntax.exp_map e2,
          find_exp RelSyntax.exp_map e3 )
      in
      F.fprintf fmt.strncpy "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | Memmove (e1, e2, e3, _) ->
      let e1_id, e2_id, e3_id =
        ( find_exp RelSyntax.exp_map e1,
          find_exp RelSyntax.exp_map e2,
          find_exp RelSyntax.exp_map e3 )
      in
      F.fprintf fmt.strncpy "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | BufferOverrunLib (_, _, _) -> F.fprintf fmt.strncpy "%s\n" id
  | AllocSize (_, _, _) | Printf (_, _, _) -> F.fprintf fmt.taint "%s\n" id

let close_formatters fmt channels =
  F.pp_print_flush fmt.alarm ();
  F.pp_print_flush fmt.deref_exp ();
  F.pp_print_flush fmt.array_exp ();
  List.iter close_out channels

let print_alarm analysis alarms =
  let alarms = Report.get alarms Report.UnProven in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  let oc_alarm = open_out (dirname ^ "/SparrowAlarm.facts") in
  let oc_array_exp = open_out (dirname ^ "/AlarmArrayExp.facts") in
  let oc_deref_exp = open_out (dirname ^ "/AlarmDerefExp.facts") in
  let oc_div_exp = open_out (dirname ^ "/AlarmDivExp.facts") in
  let oc_strcpy = open_out (dirname ^ "/AlarmStrcpy.facts") in
  let oc_strncpy = open_out (dirname ^ "/AlarmStrncpy.facts") in
  let oc_strcat = open_out (dirname ^ "/AlarmStrcat.facts") in
  let oc_taint = open_out (dirname ^ "/AlarmTaint.facts") in
  let fmt =
    {
      alarm = F.formatter_of_out_channel oc_alarm;
      array_exp = F.formatter_of_out_channel oc_array_exp;
      deref_exp = F.formatter_of_out_channel oc_deref_exp;
      div_exp = F.formatter_of_out_channel oc_div_exp;
      strcpy = F.formatter_of_out_channel oc_strcpy;
      strncpy = F.formatter_of_out_channel oc_strncpy;
      strcat = F.formatter_of_out_channel oc_strcat;
      taint = F.formatter_of_out_channel oc_taint;
    }
  in
  ignore
    (List.fold_left
       (fun set alarm ->
         match alarm.Report.src with
         | Some (src_node, _) when not (AlarmSet.mem (src_node, alarm.node) set)
           ->
             pp_alarm_exp fmt alarm.exp;
             let a_id = Hashtbl.find alarm_exp_map alarm.exp in
             F.fprintf fmt.alarm "%a\t%a\t%s\n" Node.pp src_node Node.pp
               alarm.node a_id;
             AlarmSet.add (src_node, alarm.node) set
         | _ -> set)
       AlarmSet.empty alarms);
  close_formatters fmt [ oc_alarm; oc_array_exp; oc_deref_exp ]
