open BasicDom
module F = Format
module L = Logging
module Analysis = SparseAnalysis.Make (ItvSem)
module G = Analysis.DUGraph
module TaintAnalysis = SparseAnalysis.Make (TaintSem)
module Table = TaintAnalysis.Table

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

module SCC = Graph.Components.Make (G)
module Worklist = Worklist.Make (G)

let cycle_elim dug =
  (* to find backedges *)
  let worklist = Worklist.init dug in
  let dug =
    G.update_loopheads (Worklist.loopheads worklist) dug
    |> G.update_backedges (Worklist.backedges worklist)
  in
  let backedges = G.backedges dug in
  let dug =
    BatMap.foldi
      (fun lh bes dug ->
        List.fold_left
          (fun dug pred -> G.remove_edge pred lh dug)
          dug
          (bes : Node.t list))
      backedges dug
  in
  (* sanity check *)
  SCC.scc_list dug
  |> List.iter (fun scc ->
         let length = List.length scc in
         if length > 1 then (
           let _ = prerr_endline (string_of_int length) in
           List.iter (fun node -> prerr_endline (Node.to_string node)) scc;
           assert false));
  dug

type formtter_of_patron = {
  path : F.formatter;
  evallv : F.formatter;
  eval : F.formatter;
  memory : F.formatter;
  arrayval : F.formatter;
  conststr : F.formatter;
}

let loc_map = Hashtbl.create 1000

let loc_count = ref 0

let new_loc_id loc =
  let id = "Loc-" ^ string_of_int !loc_count in
  incr loc_count;
  Hashtbl.add loc_map loc id;
  id

let val_map = Hashtbl.create 1000

let val_count = ref 0

let new_val_id v =
  let id = "Val-" ^ string_of_int !val_count in
  incr val_count;
  Hashtbl.add val_map v id;
  id

let str_map = Hashtbl.create 1000

let str_count = ref 0

let new_str_id str =
  let id = "Str-" ^ string_of_int !str_count in
  incr str_count;
  Hashtbl.add str_map str id;
  id

let pp_cmd_sems fmt global inputmem outputmem n =
  match InterCfg.cmdof global.Global.icfg n with
  | Cset (lv, e, _) ->
      let pid = Node.get_pid n in
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let e_id = Hashtbl.find RelSyntax.exp_map e in
      let loc = ItvSem.eval_lv pid lv global.Global.mem in
      let loc_id =
        if Hashtbl.mem loc_map loc then Hashtbl.find loc_map loc
        else new_loc_id loc
      in
      let v = TaintDom.Mem.lookup loc outputmem in
      let val_id =
        if Hashtbl.mem val_map v then Hashtbl.find val_map v else new_val_id v
      in
      F.fprintf fmt.evallv "%a\t%s\t%s\n" Node.pp n lv_id loc_id;
      F.fprintf fmt.eval "%a\t%s\t%s\n" Node.pp n e_id val_id;
      F.fprintf fmt.memory "%a\t%s\t%s\n" Node.pp n loc_id val_id
  | Calloc (lv, Array size, _, _) ->
      let pid = Node.get_pid n in
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let size_e_id = Hashtbl.find RelSyntax.exp_map size in
      let loc = ItvSem.eval_lv pid lv global.Global.mem in
      let loc_id =
        if Hashtbl.mem loc_map loc then Hashtbl.find loc_map loc
        else new_loc_id loc
      in
      let size_val = TaintSem.eval pid size global.Global.mem inputmem in
      let size_val_id =
        if Hashtbl.mem val_map size_val then Hashtbl.find val_map size_val
        else new_val_id size_val
      in
      let array_val = TaintDom.Mem.lookup loc outputmem in
      let array_val_id =
        if Hashtbl.mem val_map array_val then Hashtbl.find val_map array_val
        else new_val_id array_val
      in
      F.fprintf fmt.evallv "%a\t%s\t%s\n" Node.pp n lv_id loc_id;
      F.fprintf fmt.eval "%a\t%s\t%s\n" Node.pp n size_e_id size_val_id;
      F.fprintf fmt.memory "%a\t%s\t%s\n" Node.pp n loc_id array_val_id;
      F.fprintf fmt.arrayval "%s\t%s\n" array_val_id size_val_id
  | Csalloc (lv, s, _) ->
      let pid = Node.get_pid n in
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let s_id =
        if Hashtbl.mem str_map s then Hashtbl.find str_map s else new_str_id s
      in
      let loc = ItvSem.eval_lv pid lv global.Global.mem in
      let loc_id =
        if Hashtbl.mem loc_map loc then Hashtbl.find loc_map loc
        else new_loc_id loc
      in
      let v = TaintDom.Mem.lookup loc inputmem in
      let val_id =
        if Hashtbl.mem val_map v then Hashtbl.find val_map v else new_val_id v
      in
      F.fprintf fmt.evallv "%a\t%s\t%s\n" Node.pp n lv_id loc_id;
      F.fprintf fmt.memory "%a\t%s\t%s\n" Node.pp n loc_id val_id;
      F.fprintf fmt.conststr "%s\t%s\n" val_id s_id
  | Ccall (lv_opt, (Lval (Var _, NoOffset) as e), _, _) ->
      let pid = Node.get_pid n in
      let e_id = Hashtbl.find RelSyntax.exp_map e in
      if Option.is_some lv_opt then (
        let lv = Option.get lv_opt in
        let lv_id = Hashtbl.find RelSyntax.lv_map lv in
        let loc = ItvSem.eval_lv pid lv global.Global.mem in
        let loc_id =
          if Hashtbl.mem loc_map loc then Hashtbl.find loc_map loc
          else new_loc_id loc
        in
        let v = TaintDom.Mem.lookup loc outputmem in
        let val_id =
          if Hashtbl.mem val_map v then Hashtbl.find val_map v else new_val_id v
        in
        F.fprintf fmt.evallv "%a\t%s\t%s\n" Node.pp n lv_id loc_id;
        F.fprintf fmt.eval "%a\t%s\t%s\n" Node.pp n e_id val_id;
        F.fprintf fmt.memory "%a\t%s\t%s\n" Node.pp n loc_id val_id)
  | _ -> ()

let print_maps dirname =
  let oc_loc_text = open_out (dirname ^ "/Loc.map") in
  let oc_val_text = open_out (dirname ^ "/Val.map") in
  let oc_str_text = open_out (dirname ^ "/Str.map") in
  let loc_fmt = F.formatter_of_out_channel oc_loc_text in
  let val_fmt = F.formatter_of_out_channel oc_val_text in
  let str_fmt = F.formatter_of_out_channel oc_str_text in
  Hashtbl.iter
    (fun loc id -> F.fprintf loc_fmt "%s\t%a\n" id PowLoc.pp loc)
    loc_map;
  Hashtbl.iter
    (fun v id -> F.fprintf val_fmt "%s\t%a\n" id TaintDom.Val.pp v)
    val_map;
  Hashtbl.iter (fun str id -> F.fprintf str_fmt "%s\t%s\n" id str) str_map;
  F.pp_print_flush loc_fmt ();
  F.pp_print_flush val_fmt ();
  F.pp_print_flush str_fmt ();
  close_out oc_loc_text;
  close_out oc_val_text;
  close_out oc_str_text

let print analysis global dug alarms =
  let dug = G.copy dug in
  let alarms = Report.get alarms Report.UnProven in
  let dug =
    if !Options.extract_datalog_fact_full_no_opt then dug
    else optimize alarms dug
  in
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
  let oc_path = open_out (dirname ^ "/DUPath.facts") in
  let oc_tc = open_out (dirname ^ "/TrueCond.facts") in
  let oc_tb = open_out (dirname ^ "/TrueBranch.facts") in
  let oc_fc = open_out (dirname ^ "/FalseCond.facts") in
  let oc_fb = open_out (dirname ^ "/FalseBranch.facts") in
  let oc_loophead = open_out (dirname ^ "/LoopHead.facts") in
  let fmt_edge = Format.formatter_of_out_channel oc_edge in
  let fmt_path = Format.formatter_of_out_channel oc_path in
  let fmt_tc = Format.formatter_of_out_channel oc_tc in
  let fmt_tb = Format.formatter_of_out_channel oc_tb in
  let fmt_fc = Format.formatter_of_out_channel oc_fc in
  let fmt_fb = Format.formatter_of_out_channel oc_fb in
  let fmt_loophead = Format.formatter_of_out_channel oc_loophead in
  G.iter_edges
    (fun src dst ->
      if
        BatSet.mem dst (G.loopheads dug)
        && Node.get_cfgnode dst |> IntraCfg.is_entry |> not
        && Node.get_cfgnode dst |> IntraCfg.is_exit |> not
      then F.fprintf fmt_loophead "%a\n" Node.pp dst;
      if PowNode.mem dst true_branch then (
        F.fprintf fmt_tc "%a\n" Node.pp src;
        F.fprintf fmt_tb "%a\t%a\n" Node.pp src Node.pp dst)
      else if PowNode.mem dst false_branch then (
        F.fprintf fmt_fc "%a\n" Node.pp src;
        F.fprintf fmt_fb "%a\t%a\n" Node.pp src Node.pp dst)
      else F.fprintf fmt_edge "%a\t%a\n" Node.pp src Node.pp dst)
    dug;
  let tc = G.transitive_closure dug in
  G.iter_edges
    (fun src dst -> F.fprintf fmt_path "%a\t%a\n" Node.pp src Node.pp dst)
    tc;
  List.iter
    (fun x -> F.pp_print_flush x ())
    [ fmt_edge; fmt_path; fmt_tc; fmt_tb; fmt_fc; fmt_fb; fmt_loophead ];
  print_maps dirname;
  close_out oc_edge;
  close_out oc_path;
  close_out oc_tc;
  close_out oc_tb;
  close_out oc_fc;
  close_out oc_fb

let print_sems analysis global inputof outputof dug alarms =
  let dug = G.copy dug in
  let alarms = Report.get alarms Report.UnProven in
  let dug =
    if !Options.extract_datalog_fact_full_no_opt then dug
    else optimize alarms dug
  in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  (* fmt for patron *)
  let oc_path = open_out (dirname ^ "/DUPath.facts") in
  let oc_evallv = open_out (dirname ^ "/EvalLv.facts") in
  let oc_eval = open_out (dirname ^ "/Eval.facts") in
  let oc_memory = open_out (dirname ^ "/Memory.facts") in
  let oc_arrayval = open_out (dirname ^ "/ArrayVal.facts") in
  let oc_conststr = open_out (dirname ^ "/ConstStr.facts") in
  let fmt =
    {
      path = F.formatter_of_out_channel oc_path;
      evallv = F.formatter_of_out_channel oc_evallv;
      eval = F.formatter_of_out_channel oc_eval;
      memory = F.formatter_of_out_channel oc_memory;
      arrayval = F.formatter_of_out_channel oc_arrayval;
      conststr = F.formatter_of_out_channel oc_conststr;
    }
  in
  Hashtbl.reset loc_map;
  Hashtbl.reset val_map;
  Hashtbl.reset str_map;
  G.iter_node
    (fun n ->
      pp_cmd_sems fmt global (Table.find n inputof) (Table.find n outputof) n)
    dug;
  let tc = G.transitive_closure dug in
  G.iter_edges
    (fun src dst -> F.fprintf fmt.path "%a\t%a\n" Node.pp src Node.pp dst)
    tc;
  print_maps dirname;
  F.pp_print_flush fmt.evallv ();
  F.pp_print_flush fmt.eval ();
  F.pp_print_flush fmt.memory ();
  F.pp_print_flush fmt.arrayval ();
  F.pp_print_flush fmt.conststr ();
  close_out oc_path;
  close_out oc_evallv;
  close_out oc_eval;
  close_out oc_memory;
  close_out oc_arrayval;
  close_out oc_conststr

module AlarmSet = Set.Make (struct
  type t = Node.t * Node.t [@@deriving compare]
end)

type formatter = {
  start : F.formatter;
  alarm : F.formatter;
  array_exp : F.formatter;
  deref_exp : F.formatter;
  mul_exp : F.formatter;
  div_exp : F.formatter;
  strcpy : F.formatter;
  strncpy : F.formatter;
  memcpy : F.formatter;
  memmove : F.formatter;
  memchr : F.formatter;
  strncmp : F.formatter;
  sprintf : F.formatter;
  sprintf_err_cons : F.formatter;
  io_err_cons : F.formatter;
  bufferoverrunlib : F.formatter;
  strcat : F.formatter;
  allocsize : F.formatter;
  printf : F.formatter;
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

let ikind_of_typ = function Cil.TInt (ik, _) -> Some ik | _ -> None

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
      F.fprintf fmt.memcpy "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | Memmove (e1, e2, e3, _) ->
      let e1_id, e2_id, e3_id =
        ( find_exp RelSyntax.exp_map e1,
          find_exp RelSyntax.exp_map e2,
          find_exp RelSyntax.exp_map e3 )
      in
      F.fprintf fmt.memmove "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | BufferOverrunLib (("memchr" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.memchr "%s\t%s\t%s\n" id e0_id e1_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | BufferOverrunLib (("strncmp" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      let e2_id = List.nth el 2 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.strncmp "%s\t%s\t%s\t%s\n" id e0_id e1_id e2_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e2_id
  | BufferOverrunLib (("sprintf" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.sprintf "%s\t%s\t%s\n" id e0_id e1_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | AllocSize (_, e1, _) ->
      let e1_id = find_exp RelSyntax.exp_map e1 in
      F.fprintf fmt.allocsize "%s\t%s\n" id e1_id;
      F.fprintf fmt.taint "%s\t%s\n" id e1_id
  | Printf (_, e1, _) ->
      let e1_id = find_exp RelSyntax.exp_map e1 in
      F.fprintf fmt.printf "%s\t%s\n" id e1_id;
      F.fprintf fmt.taint "%s\t%s\n" id e1_id
  | BufferOverrunLib (name, _, _) -> failwith name
  | _ -> ()

let close_formatters fmt channels =
  F.pp_print_flush fmt.start ();
  F.pp_print_flush fmt.alarm ();
  F.pp_print_flush fmt.array_exp ();
  F.pp_print_flush fmt.deref_exp ();
  F.pp_print_flush fmt.mul_exp ();
  F.pp_print_flush fmt.div_exp ();
  F.pp_print_flush fmt.strcpy ();
  F.pp_print_flush fmt.strncpy ();
  F.pp_print_flush fmt.strcat ();
  F.pp_print_flush fmt.memcpy ();
  F.pp_print_flush fmt.memmove ();
  F.pp_print_flush fmt.memchr ();
  F.pp_print_flush fmt.strncmp ();
  F.pp_print_flush fmt.sprintf ();
  F.pp_print_flush fmt.sprintf_err_cons ();
  F.pp_print_flush fmt.io_err_cons ();
  F.pp_print_flush fmt.bufferoverrunlib ();
  F.pp_print_flush fmt.allocsize ();
  F.pp_print_flush fmt.printf ();
  F.pp_print_flush fmt.taint ();
  List.iter close_out channels

let print_alarm analysis alarms =
  let alarms = Report.get alarms Report.UnProven in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  let oc_start = open_out (dirname ^ "/Start.facts") in
  let oc_alarm = open_out (dirname ^ "/SparrowAlarm.facts") in
  let oc_array_exp = open_out (dirname ^ "/AlarmArrayExp.facts") in
  let oc_deref_exp = open_out (dirname ^ "/AlarmDerefExp.facts") in
  let oc_mul_exp = open_out (dirname ^ "/AlarmMulExp.facts") in
  let oc_div_exp = open_out (dirname ^ "/AlarmDivExp.facts") in
  let oc_strcpy = open_out (dirname ^ "/AlarmStrcpy.facts") in
  let oc_strncpy = open_out (dirname ^ "/AlarmStrncpy.facts") in
  let oc_memmove = open_out (dirname ^ "/AlarmMemmove.facts") in
  let oc_memcpy = open_out (dirname ^ "/AlarmMemcpy.facts") in
  let oc_memchr = open_out (dirname ^ "/AlarmMemchr.facts") in
  let oc_strncmp = open_out (dirname ^ "/AlarmStrncmp.facts") in
  let oc_sprintf = open_out (dirname ^ "/AlarmSprintf.facts") in
  let oc_sprintf_err_cons =
    open_out (dirname ^ "/SprintfErrorConstraint.facts")
  in
  let oc_io_err_cons = open_out (dirname ^ "/IOErrorConstraint.facts") in
  let oc_bufferoverrunlib =
    open_out (dirname ^ "/AlarmBufferOverrunLib.facts")
  in
  let oc_strcat = open_out (dirname ^ "/AlarmStrcat.facts") in
  let oc_allocsize = open_out (dirname ^ "/AlarmAllocSize.facts") in
  let oc_printf = open_out (dirname ^ "/AlarmPrintf.facts") in
  let oc_taint = open_out (dirname ^ "/AlarmTaint.facts") in
  let fmt =
    {
      start = F.formatter_of_out_channel oc_start;
      alarm = F.formatter_of_out_channel oc_alarm;
      array_exp = F.formatter_of_out_channel oc_array_exp;
      deref_exp = F.formatter_of_out_channel oc_deref_exp;
      mul_exp = F.formatter_of_out_channel oc_mul_exp;
      div_exp = F.formatter_of_out_channel oc_div_exp;
      strcpy = F.formatter_of_out_channel oc_strcpy;
      strncpy = F.formatter_of_out_channel oc_strncpy;
      memcpy = F.formatter_of_out_channel oc_memcpy;
      memmove = F.formatter_of_out_channel oc_memmove;
      memchr = F.formatter_of_out_channel oc_memchr;
      strncmp = F.formatter_of_out_channel oc_strncmp;
      sprintf = F.formatter_of_out_channel oc_sprintf;
      sprintf_err_cons = F.formatter_of_out_channel oc_sprintf_err_cons;
      io_err_cons = F.formatter_of_out_channel oc_io_err_cons;
      bufferoverrunlib = F.formatter_of_out_channel oc_bufferoverrunlib;
      strcat = F.formatter_of_out_channel oc_strcat;
      allocsize = F.formatter_of_out_channel oc_allocsize;
      printf = F.formatter_of_out_channel oc_printf;
      taint = F.formatter_of_out_channel oc_taint;
    }
  in
  F.fprintf fmt.start "%s\n" "_G_-ENTRY";
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
  close_formatters fmt
    [
      oc_start;
      oc_alarm;
      oc_array_exp;
      oc_deref_exp;
      oc_mul_exp;
      oc_div_exp;
      oc_strcpy;
      oc_strncpy;
      oc_memmove;
      oc_memcpy;
      oc_memchr;
      oc_strncmp;
      oc_sprintf;
      oc_sprintf_err_cons;
      oc_io_err_cons;
      oc_bufferoverrunlib;
      oc_strcat;
      oc_allocsize;
      oc_printf;
      oc_taint;
    ]

let pp_taint_alarm_exp global inputmem node fmt aexp =
  let id = new_alarm_exp_id aexp in
  let pid = Node.get_pid node in
  match aexp with
  | AlarmExp.ArrayExp (l, e, _) ->
      let l_id = find_lv RelSyntax.lv_map l in
      let e_id = find_exp RelSyntax.exp_map e in
      F.fprintf fmt.array_exp "%s\t%s\t%s\n" id l_id e_id
  | DerefExp (e, _) ->
      let e_id = find_exp RelSyntax.exp_map e in
      F.fprintf fmt.deref_exp "%s\t%s\n" id e_id
  | MulExp (e1, e2, _) ->
      let v1 = TaintSem.eval pid e1 global.Global.mem inputmem in
      let v2 = TaintSem.eval pid e2 global.Global.mem inputmem in
      let v1_id =
        if Hashtbl.mem val_map v1 then Hashtbl.find val_map v1
        else new_val_id v1
      in
      let v2_id =
        if Hashtbl.mem val_map v2 then Hashtbl.find val_map v2
        else new_val_id v2
      in
      let t1 =
        Cil.typeOf e1 |> ikind_of_typ
        |> Option.map Cil.bytesSizeOfInt
        |> Option.value ~default:0
      in
      let t2 =
        Cil.typeOf e2 |> ikind_of_typ
        |> Option.map Cil.bytesSizeOfInt
        |> Option.value ~default:0
      in
      (* TODO: unsigned long long *)
      let int_max = max t1 t2 * 8 |> BatInt64.of_int |> BatInt64.pow 2L in
      let int_max =
        if int_max = 0L then Int64.max_int else BatInt64.(int_max - 1L)
      in
      F.fprintf fmt.io_err_cons "%a\t(> (* (IntVal %s) (IntVal %s)) %Ld)\n"
        Node.pp node v1_id v2_id int_max;
      let e1_id, e2_id =
        (find_exp RelSyntax.exp_map e1, find_exp RelSyntax.exp_map e2)
      in
      F.fprintf fmt.mul_exp "%s\t%s\t%s\n" id e1_id e2_id
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
      F.fprintf fmt.memcpy "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | Memmove (e1, e2, e3, _) ->
      let e1_id, e2_id, e3_id =
        ( find_exp RelSyntax.exp_map e1,
          find_exp RelSyntax.exp_map e2,
          find_exp RelSyntax.exp_map e3 )
      in
      F.fprintf fmt.memmove "%s\t%s\t%s\t%s\n" id e1_id e2_id e3_id
  | BufferOverrunLib (("memchr" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.memchr "%s\t%s\t%s\n" id e0_id e1_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | BufferOverrunLib (("strncmp" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      let e2_id = List.nth el 2 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.strncmp "%s\t%s\t%s\t%s\n" id e0_id e1_id e2_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e2_id
  | BufferOverrunLib (("sprintf" as name), el, _) ->
      let arg0 = List.hd el in
      let arr_arg0 = TaintSem.eval pid arg0 global.Global.mem inputmem in
      let arr_val_id =
        if Hashtbl.mem val_map arr_arg0 then Hashtbl.find val_map arr_arg0
        else new_val_id arr_arg0
      in
      let strlen_exp =
        List.tl el
        |> List.map (fun arg ->
               TaintSem.eval pid arg global.Global.mem inputmem
               |> (fun v ->
                    if Hashtbl.mem val_map v then Hashtbl.find val_map v
                    else new_val_id v)
               |> F.sprintf "(StrLen %s)")
        |> String.concat " "
      in
      F.fprintf fmt.sprintf_err_cons "(< (SizeOf %s) (+ %s))\n" arr_val_id
        strlen_exp;
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.sprintf "%s\t%s\t%s\n" id e0_id e1_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | AllocSize (_, e1, _) ->
      let e1_id = find_exp RelSyntax.exp_map e1 in
      F.fprintf fmt.allocsize "%s\t%s\n" id e1_id;
      F.fprintf fmt.taint "%s\t%s\n" id e1_id
  | Printf (_, e1, _) ->
      let e1_id = find_exp RelSyntax.exp_map e1 in
      F.fprintf fmt.printf "%s\t%s\n" id e1_id;
      F.fprintf fmt.taint "%s\t%s\n" id e1_id
  | BufferOverrunLib (name, _, _) -> failwith name

let print_taint_alarm analysis global inputof alarms =
  let alarms = Report.get alarms Report.UnProven in
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  let oc_start = open_out (dirname ^ "/Start.facts") in
  let oc_alarm = open_out (dirname ^ "/SparrowAlarm.facts") in
  let oc_array_exp = open_out (dirname ^ "/AlarmArrayExp.facts") in
  let oc_deref_exp = open_out (dirname ^ "/AlarmDerefExp.facts") in
  let oc_mul_exp = open_out (dirname ^ "/AlarmMulExp.facts") in
  let oc_div_exp = open_out (dirname ^ "/AlarmDivExp.facts") in
  let oc_strcpy = open_out (dirname ^ "/AlarmStrcpy.facts") in
  let oc_strncpy = open_out (dirname ^ "/AlarmStrncpy.facts") in
  let oc_memmove = open_out (dirname ^ "/AlarmMemmove.facts") in
  let oc_memcpy = open_out (dirname ^ "/AlarmMemcpy.facts") in
  let oc_memchr = open_out (dirname ^ "/AlarmMemchr.facts") in
  let oc_strncmp = open_out (dirname ^ "/AlarmStrncmp.facts") in
  let oc_sprintf = open_out (dirname ^ "/AlarmSprintf.facts") in
  let oc_sprintf_err_cons =
    open_out (dirname ^ "/SprintfErrorConstraint.facts")
  in
  let oc_io_err_cons = open_out (dirname ^ "/IOErrorConstraint.facts") in
  let oc_bufferoverrunlib =
    open_out (dirname ^ "/AlarmBufferOverrunLib.facts")
  in
  let oc_strcat = open_out (dirname ^ "/AlarmStrcat.facts") in
  let oc_allocsize = open_out (dirname ^ "/AlarmAllocSize.facts") in
  let oc_printf = open_out (dirname ^ "/AlarmPrintf.facts") in
  let oc_taint = open_out (dirname ^ "/AlarmTaint.facts") in
  let fmt =
    {
      start = F.formatter_of_out_channel oc_start;
      alarm = F.formatter_of_out_channel oc_alarm;
      array_exp = F.formatter_of_out_channel oc_array_exp;
      deref_exp = F.formatter_of_out_channel oc_deref_exp;
      mul_exp = F.formatter_of_out_channel oc_mul_exp;
      div_exp = F.formatter_of_out_channel oc_div_exp;
      strcpy = F.formatter_of_out_channel oc_strcpy;
      strncpy = F.formatter_of_out_channel oc_strncpy;
      memcpy = F.formatter_of_out_channel oc_memcpy;
      memmove = F.formatter_of_out_channel oc_memmove;
      memchr = F.formatter_of_out_channel oc_memchr;
      strncmp = F.formatter_of_out_channel oc_strncmp;
      sprintf = F.formatter_of_out_channel oc_sprintf;
      sprintf_err_cons = F.formatter_of_out_channel oc_sprintf_err_cons;
      io_err_cons = F.formatter_of_out_channel oc_io_err_cons;
      bufferoverrunlib = F.formatter_of_out_channel oc_bufferoverrunlib;
      strcat = F.formatter_of_out_channel oc_strcat;
      allocsize = F.formatter_of_out_channel oc_allocsize;
      printf = F.formatter_of_out_channel oc_printf;
      taint = F.formatter_of_out_channel oc_taint;
    }
  in
  F.fprintf fmt.start "%s\n" "_G_-ENTRY";
  ignore
    (List.fold_left
       (fun set alarm ->
         match alarm.Report.src with
         | Some (src_node, _) when not (AlarmSet.mem (src_node, alarm.node) set)
           ->
             pp_taint_alarm_exp global
               (Table.find alarm.node inputof)
               alarm.node fmt alarm.exp;
             let a_id = Hashtbl.find alarm_exp_map alarm.exp in
             F.fprintf fmt.alarm "%a\t%a\t%s\n" Node.pp src_node Node.pp
               alarm.node a_id;
             AlarmSet.add (src_node, alarm.node) set
         | _ -> set)
       AlarmSet.empty alarms);
  close_formatters fmt
    [
      oc_start;
      oc_alarm;
      oc_array_exp;
      oc_deref_exp;
      oc_mul_exp;
      oc_div_exp;
      oc_strcpy;
      oc_strncpy;
      oc_memmove;
      oc_memcpy;
      oc_memchr;
      oc_strncmp;
      oc_sprintf;
      oc_sprintf_err_cons;
      oc_io_err_cons;
      oc_bufferoverrunlib;
      oc_strcat;
      oc_allocsize;
      oc_printf;
      oc_taint;
    ]
