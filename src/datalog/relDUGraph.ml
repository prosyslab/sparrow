open BasicDom
open ProsysCil
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
      (try
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
                   ( G.PowLoc.fold
                       (fun u -> ReachingDef.add (p, u))
                       uses_pred works,
                     ReachingDef.add (p, use) results )
                 else
                   ( ReachingDef.add (p, use) works,
                     ReachingDef.add (p, use) results )
             else if p = InterCfg.start_node then
               (works, ReachingDef.add (p, use) results)
             else (works, results))
           g node (works, results)
       with Invalid_argument _ -> (works, results))
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

let optimize ?(verbose = true) alarms g =
  if verbose then
    L.info "%d nodes and %d edges before optimization\n" (G.nb_node g)
      (G.nb_edge g);
  let g = optimize_reachability alarms g in
  if verbose then
    L.info "%d nodes and %d edges after reachability\n" (G.nb_node g)
      (G.nb_edge g);
  let g = reachability2 alarms g in
  if verbose then
    L.info "%d nodes and %d edges after reachability2\n" (G.nb_node g)
      (G.nb_edge g);
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

type formatter_of_patron = {
  deduedge : F.formatter;
  duedge : F.formatter;
  dupath : F.formatter;
}

let loc_map = Hashtbl.create 1000
let loc_count = ref 0

let new_loc_id loc =
  let id = "Loc-" ^ string_of_int !loc_count in
  incr loc_count;
  Hashtbl.add loc_map loc id;
  id

let val_count = ref 0

let new_val_id () =
  let id = "Val-" ^ string_of_int !val_count in
  incr val_count;
  id

let str_map = Hashtbl.create 1000
let str_count = ref 0

let new_str_id str =
  let id = "Str-" ^ string_of_int !str_count in
  incr str_count;
  Hashtbl.add str_map str id;
  id

let val_of_const = function
  | Cil.CInt64 (i, _, _) -> i
  | Cil.CChr c -> Char.code c |> Z.of_int
  | _ -> Z.zero (* TODO: add String, Real domain *)

let print_maps dirname =
  let oc_loc_text = open_out (dirname ^ "/Loc.map") in
  let oc_str_text = open_out (dirname ^ "/Str.map") in
  let loc_fmt = F.formatter_of_out_channel oc_loc_text in
  let str_fmt = F.formatter_of_out_channel oc_str_text in
  Hashtbl.iter
    (fun loc id -> F.fprintf loc_fmt "%s\t%a\n" id PowLoc.pp loc)
    loc_map;
  Hashtbl.iter (fun str id -> F.fprintf str_fmt "%s\t%s\n" id str) str_map;
  F.pp_print_flush loc_fmt ();
  F.pp_print_flush str_fmt ();
  close_out oc_loc_text;
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
  close_out oc_edge;
  close_out oc_path;
  close_out oc_tc;
  close_out oc_tb;
  close_out oc_fc;
  close_out oc_fb

let print_sems dirname dug =
  (* fmt for patron *)
  let oc_deduedge = open_out (dirname ^ "/DetailedDUEdge.facts") in
  let oc_duedge = open_out (dirname ^ "/DUEdge.facts") in
  let oc_dupath = open_out (dirname ^ "/DUPath.facts") in
  let fmt =
    {
      deduedge = F.formatter_of_out_channel oc_deduedge;
      duedge = F.formatter_of_out_channel oc_duedge;
      dupath = F.formatter_of_out_channel oc_dupath;
    }
  in
  G.iter_edges_e
    (fun src dst locset ->
      if Hashtbl.mem loc_map locset then
        F.fprintf fmt.deduedge "%a\t%a\t%s\n" Node.pp src Node.pp dst
          (Hashtbl.find loc_map locset)
      else
        F.fprintf fmt.deduedge "%a\t%a\t%a\n" Node.pp src Node.pp dst PowLoc.pp
          locset;
      F.fprintf fmt.duedge "%a\t%a\n" Node.pp src Node.pp dst)
    dug;
  F.pp_print_flush fmt.deduedge ();
  F.pp_print_flush fmt.duedge ();
  F.pp_print_flush fmt.dupath ();
  close_out oc_deduedge;
  close_out oc_duedge;
  close_out oc_dupath

module AlarmSet = Set.Make (struct
  type t = Node.t * Node.t [@@deriving compare]
end)

type formatter = {
  start : F.formatter;
  alarm : F.formatter;
  array_exp : F.formatter;
  deref_exp : F.formatter;
  pio_exp : F.formatter;
  mio_exp : F.formatter;
  tio_exp : F.formatter;
  sio_exp : F.formatter;
  cio_exp : F.formatter;
  div_exp : F.formatter;
  strcpy : F.formatter;
  strncpy : F.formatter;
  memcpy : F.formatter;
  memmove : F.formatter;
  memchr : F.formatter;
  strncmp : F.formatter;
  sprintf : F.formatter;
  fread : F.formatter;
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

let find_patron_exp exp_map (n, e) =
  try Hashtbl.find exp_map (n, e) with _ -> "UnknownExp-" ^ CilHelper.s_exp e

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
  | DivExp (Cil.BinOp (_, e1, e2, _), _) ->
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
  | BufferOverrunLib (("fread" as name), el, _) ->
      let e0_id = List.nth el 0 |> find_exp RelSyntax.exp_map in
      let e1_id = List.nth el 1 |> find_exp RelSyntax.exp_map in
      let e2_id = List.nth el 2 |> find_exp RelSyntax.exp_map in
      F.fprintf fmt.fread "%s\t%s\t%s\n" id e0_id e1_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e2_id
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
  F.pp_print_flush fmt.pio_exp ();
  F.pp_print_flush fmt.mio_exp ();
  F.pp_print_flush fmt.tio_exp ();
  F.pp_print_flush fmt.sio_exp ();
  F.pp_print_flush fmt.cio_exp ();
  F.pp_print_flush fmt.div_exp ();
  F.pp_print_flush fmt.strcpy ();
  F.pp_print_flush fmt.strncpy ();
  F.pp_print_flush fmt.strcat ();
  F.pp_print_flush fmt.memcpy ();
  F.pp_print_flush fmt.memmove ();
  F.pp_print_flush fmt.memchr ();
  F.pp_print_flush fmt.strncmp ();
  F.pp_print_flush fmt.sprintf ();
  F.pp_print_flush fmt.fread ();
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
  let oc_pio_exp = open_out (dirname ^ "/AlarmPlusIOExp.facts") in
  let oc_mio_exp = open_out (dirname ^ "/AlarmMinusIOExp.facts") in
  let oc_tio_exp = open_out (dirname ^ "/AlarmMultIOExp.facts") in
  let oc_sio_exp = open_out (dirname ^ "/AlarmShiftIOExp.facts") in
  let oc_cio_exp = open_out (dirname ^ "/AlarmCastIOExp.facts") in
  let oc_div_exp = open_out (dirname ^ "/AlarmDivExp.facts") in
  let oc_strcpy = open_out (dirname ^ "/AlarmStrcpy.facts") in
  let oc_strncpy = open_out (dirname ^ "/AlarmStrncpy.facts") in
  let oc_memmove = open_out (dirname ^ "/AlarmMemmove.facts") in
  let oc_memcpy = open_out (dirname ^ "/AlarmMemcpy.facts") in
  let oc_memchr = open_out (dirname ^ "/AlarmMemchr.facts") in
  let oc_strncmp = open_out (dirname ^ "/AlarmStrncmp.facts") in
  let oc_sprintf = open_out (dirname ^ "/AlarmSprintf.facts") in
  let oc_fread = open_out (dirname ^ "/AlarmFread.facts") in
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
      pio_exp = F.formatter_of_out_channel oc_pio_exp;
      mio_exp = F.formatter_of_out_channel oc_mio_exp;
      tio_exp = F.formatter_of_out_channel oc_tio_exp;
      sio_exp = F.formatter_of_out_channel oc_sio_exp;
      cio_exp = F.formatter_of_out_channel oc_cio_exp;
      div_exp = F.formatter_of_out_channel oc_div_exp;
      strcpy = F.formatter_of_out_channel oc_strcpy;
      strncpy = F.formatter_of_out_channel oc_strncpy;
      memcpy = F.formatter_of_out_channel oc_memcpy;
      memmove = F.formatter_of_out_channel oc_memmove;
      memchr = F.formatter_of_out_channel oc_memchr;
      strncmp = F.formatter_of_out_channel oc_strncmp;
      sprintf = F.formatter_of_out_channel oc_sprintf;
      fread = F.formatter_of_out_channel oc_fread;
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
      oc_pio_exp;
      oc_mio_exp;
      oc_tio_exp;
      oc_sio_exp;
      oc_cio_exp;
      oc_div_exp;
      oc_strcpy;
      oc_strncpy;
      oc_memmove;
      oc_memcpy;
      oc_memchr;
      oc_strncmp;
      oc_sprintf;
      oc_fread;
      oc_bufferoverrunlib;
      oc_strcat;
      oc_allocsize;
      oc_printf;
      oc_taint;
    ]

module LvSet = Set.Make (struct
  type t = Cil.lval

  let compare = compare
end)

let rec unbox_exp = function
  | Cil.AddrOfLabel _ | Cil.SizeOf _ | Cil.AlignOf _ | Cil.SizeOfStr _
  | Cil.Const _ ->
      LvSet.empty
  | Cil.UnOp (_, e, _) | Cil.SizeOfE e | Cil.CastE (_, e) | Cil.AlignOfE e ->
      unbox_exp e
  | Cil.Lval l | Cil.StartOf l | Cil.AddrOf l -> LvSet.singleton l
  | Cil.BinOp (_, e1, e2, _) -> LvSet.union (unbox_exp e1) (unbox_exp e2)
  | Cil.Question (e1, e2, e3, _) ->
      LvSet.union (unbox_exp e1) (unbox_exp e2) |> LvSet.union (unbox_exp e3)

let rec unbox_exp = function
  | Cil.AddrOfLabel _ | Cil.SizeOf _ | Cil.AlignOf _ | Cil.SizeOfStr _
  | Cil.Const _ ->
      LvSet.empty
  | Cil.UnOp (_, e, _) | Cil.SizeOfE e | Cil.CastE (_, e) | Cil.AlignOfE e ->
      unbox_exp e
  | Cil.Lval l | Cil.StartOf l | Cil.AddrOf l -> LvSet.singleton l
  | Cil.BinOp (_, e1, e2, _) -> LvSet.union (unbox_exp e1) (unbox_exp e2)
  | Cil.Question (e1, e2, e3, _) ->
      LvSet.union (unbox_exp e1) (unbox_exp e2) |> LvSet.union (unbox_exp e3)

let pp_taint_alarm_exp fmt aexp =
  let id = new_alarm_exp_id aexp in
  match aexp with
  | AlarmExp.ArrayExp (l, e, _) ->
      let l_id = find_lv RelSyntax.lv_map l in
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      let e_id = find_exp RelSyntax.exp_map e' in
      let lvs = unbox_exp e in
      let lv_ids =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs ""
      in
      F.fprintf fmt.array_exp "%s\t%s\t%s%s\n" id l_id e_id lv_ids
  | DerefExp (e, _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      let e_id = find_exp RelSyntax.exp_map e' in
      let lvs = unbox_exp e in
      let lv_ids =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs ""
      in
      F.fprintf fmt.deref_exp "%s\t%s%s\n" id e_id lv_ids
  | PlusIOExp (Cil.BinOp (_, e1, e2, _), _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.pio_exp "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | MinusIOExp (Cil.BinOp (_, e1, e2, _), _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.mio_exp "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | MultIOExp (Cil.BinOp (_, e1, e2, _), _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.tio_exp "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | ShiftIOExp (Cil.BinOp (_, e1, e2, _), _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.sio_exp "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | CastIOExp (Cil.CastE (_, e), _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      let e_id = find_exp RelSyntax.exp_map e' in
      let lvs = unbox_exp e in
      let lv_ids =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs ""
      in
      F.fprintf fmt.cio_exp "%s\t%s%s\n" id e_id lv_ids
  | DivExp (Cil.BinOp (_, e1, e2, _), _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.div_exp "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | Strcpy (e1, e2, _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.strcpy "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | Strcat (e1, e2, _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.strcat "%s\t%s\t%s%s\n" id e1_id e2_id lv_ids
  | Strncpy (e1, e2, e3, _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e3' = if !Options.remove_cast then RelSyntax.remove_cast e3 else e3 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let e3_id = find_exp RelSyntax.exp_map e3' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lvs3 = unbox_exp e3 in
      let lv_ids3 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs3 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 ^ lv_ids3 in
      F.fprintf fmt.strncpy "%s\t%s\t%s\t%s%s\n" id e1_id e2_id e3_id lv_ids
  | Memcpy (e1, e2, e3, _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e3' = if !Options.remove_cast then RelSyntax.remove_cast e3 else e3 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let e3_id = find_exp RelSyntax.exp_map e3' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lvs3 = unbox_exp e3 in
      let lv_ids3 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs3 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 ^ lv_ids3 in
      F.fprintf fmt.memcpy "%s\t%s\t%s\t%s%s\n" id e1_id e2_id e3_id lv_ids
  | Memmove (e1, e2, e3, _) ->
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e3' = if !Options.remove_cast then RelSyntax.remove_cast e3 else e3 in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let e3_id = find_exp RelSyntax.exp_map e3' in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lvs3 = unbox_exp e3 in
      let lv_ids3 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs3 ""
      in
      let lv_ids = lv_ids1 ^ lv_ids2 ^ lv_ids3 in
      F.fprintf fmt.memmove "%s\t%s\t%s\t%s%s\n" id e1_id e2_id e3_id lv_ids
  | BufferOverrunLib (("memchr" as name), el, _) ->
      let e0 = List.nth el 0 in
      let e1 = List.nth el 1 in
      let e0' = if !Options.remove_cast then RelSyntax.remove_cast e0 else e0 in
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e0_id = find_exp RelSyntax.exp_map e0' in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let lvs0 = unbox_exp e0 in
      let lv_ids0 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs0 ""
      in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lv_ids = lv_ids0 ^ lv_ids1 in
      F.fprintf fmt.memchr "%s\t%s\t%s%s\n" id e0_id e1_id lv_ids;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | BufferOverrunLib (("strncmp" as name), el, _) ->
      let e0 = List.nth el 0 in
      let e1 = List.nth el 1 in
      let e2 = List.nth el 2 in
      let e0' = if !Options.remove_cast then RelSyntax.remove_cast e0 else e0 in
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e0_id = find_exp RelSyntax.exp_map e0' in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      let lvs0 = unbox_exp e0 in
      let lv_ids0 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs0 ""
      in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lvs2 = unbox_exp e2 in
      let lv_ids2 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs2 ""
      in
      let lv_ids = lv_ids0 ^ lv_ids1 ^ lv_ids2 in
      F.fprintf fmt.strncmp "%s\t%s\t%s\t%s%s\n" id e0_id e1_id e2_id lv_ids;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e2_id
  | BufferOverrunLib (("sprintf" as name), el, _) ->
      let e0 = List.nth el 0 in
      let e1 = List.nth el 1 in
      let e0' = if !Options.remove_cast then RelSyntax.remove_cast e0 else e0 in
      let e1' = if !Options.remove_cast then RelSyntax.remove_cast e1 else e1 in
      let e0_id = find_exp RelSyntax.exp_map e0' in
      let e1_id = find_exp RelSyntax.exp_map e1' in
      let lvs0 = unbox_exp e0 in
      let lv_ids0 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs0 ""
      in
      let lvs1 = unbox_exp e1 in
      let lv_ids1 =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs1 ""
      in
      let lv_ids = lv_ids0 ^ lv_ids1 in
      F.fprintf fmt.sprintf "%s\t%s\t%s%s\n" id e0_id e1_id lv_ids;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e1_id
  | BufferOverrunLib (("fread" as name), el, _) ->
      let e0 = List.nth el 0 in
      let e2 = List.nth el 2 in
      let e0' = if !Options.remove_cast then RelSyntax.remove_cast e0 else e0 in
      let e2' = if !Options.remove_cast then RelSyntax.remove_cast e2 else e2 in
      let e0_id = find_exp RelSyntax.exp_map e0' in
      let e2_id = find_exp RelSyntax.exp_map e2' in
      F.fprintf fmt.fread "%s\t%s\t%s\n" id e0_id e2_id;
      F.fprintf fmt.bufferoverrunlib "%s\t%s\t%s\n" id name e2_id
  | AllocSize (_, e, _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      let e_id = find_exp RelSyntax.exp_map e' in
      let lvs = unbox_exp e in
      let lv_ids =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs ""
      in
      F.fprintf fmt.allocsize "%s\t%s%s\n" id e_id lv_ids;
      F.fprintf fmt.taint "%s\t%s\n" id e_id
  | Printf (_, e, _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      let e_id = find_exp RelSyntax.exp_map e' in
      let lvs = unbox_exp e in
      let lv_ids =
        LvSet.fold (fun lv s -> s ^ "\t" ^ find_lv RelSyntax.lv_map lv) lvs ""
      in
      F.fprintf fmt.printf "%s\t%s%s\n" id e_id lv_ids;
      F.fprintf fmt.taint "%s\t%s\n" id e_id
  | BufferOverrunLib (name, _, _) -> failwith name
  | _ -> ()

let print_taint_alarm_in_dir dirname alarms =
  let oc_start = open_out (dirname ^ "/Start.facts") in
  let oc_alarm = open_out (dirname ^ "/SparrowAlarm.facts") in
  let oc_array_exp = open_out (dirname ^ "/AlarmArrayExp.facts") in
  let oc_deref_exp = open_out (dirname ^ "/AlarmDerefExp.facts") in
  let oc_pio_exp = open_out (dirname ^ "/AlarmPlusIOExp.facts") in
  let oc_mio_exp = open_out (dirname ^ "/AlarmMinusIOExp.facts") in
  let oc_tio_exp = open_out (dirname ^ "/AlarmMultIOExp.facts") in
  let oc_sio_exp = open_out (dirname ^ "/AlarmShiftIOExp.facts") in
  let oc_cio_exp = open_out (dirname ^ "/AlarmCastIOExp.facts") in
  let oc_div_exp = open_out (dirname ^ "/AlarmDivExp.facts") in
  let oc_strcpy = open_out (dirname ^ "/AlarmStrcpy.facts") in
  let oc_strncpy = open_out (dirname ^ "/AlarmStrncpy.facts") in
  let oc_memmove = open_out (dirname ^ "/AlarmMemmove.facts") in
  let oc_memcpy = open_out (dirname ^ "/AlarmMemcpy.facts") in
  let oc_memchr = open_out (dirname ^ "/AlarmMemchr.facts") in
  let oc_strncmp = open_out (dirname ^ "/AlarmStrncmp.facts") in
  let oc_sprintf = open_out (dirname ^ "/AlarmSprintf.facts") in
  let oc_fread = open_out (dirname ^ "/AlarmFread.facts") in
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
      pio_exp = F.formatter_of_out_channel oc_pio_exp;
      mio_exp = F.formatter_of_out_channel oc_mio_exp;
      tio_exp = F.formatter_of_out_channel oc_tio_exp;
      sio_exp = F.formatter_of_out_channel oc_sio_exp;
      cio_exp = F.formatter_of_out_channel oc_cio_exp;
      div_exp = F.formatter_of_out_channel oc_div_exp;
      strcpy = F.formatter_of_out_channel oc_strcpy;
      strncpy = F.formatter_of_out_channel oc_strncpy;
      memcpy = F.formatter_of_out_channel oc_memcpy;
      memmove = F.formatter_of_out_channel oc_memmove;
      memchr = F.formatter_of_out_channel oc_memchr;
      strncmp = F.formatter_of_out_channel oc_strncmp;
      sprintf = F.formatter_of_out_channel oc_sprintf;
      fread = F.formatter_of_out_channel oc_fread;
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
             pp_taint_alarm_exp fmt alarm.exp;
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
      oc_pio_exp;
      oc_mio_exp;
      oc_tio_exp;
      oc_sio_exp;
      oc_cio_exp;
      oc_div_exp;
      oc_strcpy;
      oc_strncpy;
      oc_memmove;
      oc_memcpy;
      oc_memchr;
      oc_strncmp;
      oc_sprintf;
      oc_fread;
      oc_bufferoverrunlib;
      oc_strcat;
      oc_allocsize;
      oc_printf;
      oc_taint;
    ]

let print_taint_alarm analysis alarms =
  L.info "print_taint_alarm - alarms:\n";
  List.iter (fun alarm -> L.info "%s\n" (Report.string_of_query alarm)) alarms;
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  print_taint_alarm_in_dir dirname alarms

let rec add_offset o orig_offset =
  match orig_offset with
  | Cil.NoOffset -> o
  | Cil.Field (f, o1) -> Cil.Field (f, add_offset o o1)
  | Cil.Index (e, o1) -> Cil.Index (e, add_offset o o1)

let append_field lv f = (fst lv, add_offset (Field (f, NoOffset)) (snd lv))
let append_index lv e = (fst lv, add_offset (Index (e, NoOffset)) (snd lv))

let rec pp_lv (fmt : RelSyntax.formatter) n lv mem =
  let pid = Node.get_pid n in
  let locs = ItvSem.eval_lv pid lv mem in
  let loc_id =
    if Hashtbl.mem loc_map locs then Hashtbl.find loc_map locs
    else new_loc_id locs
  in
  let id =
    if Hashtbl.mem RelSyntax.lv_map lv then Hashtbl.find RelSyntax.lv_map lv
    else RelSyntax.new_lv_id lv
  in
  F.fprintf fmt.evallv "%a\t%s\t%s\n" Node.pp n id loc_id;
  if lv <> RelSyntax.donotcare_lv then F.fprintf fmt.real_lv "%s\n" id;
  match lv with
  | Cil.Var vi, Cil.NoOffset ->
      if vi.Cil.vglob then
        F.fprintf fmt.RelSyntax.global_var "%s\t%s\n" id vi.vname
      else F.fprintf fmt.local_var "%s\t%s\n" id vi.vname
  | Cil.Var v, offset -> pp_offset fmt n lv (Cil.Var v, Cil.NoOffset) offset mem
  | Cil.Mem e, Cil.NoOffset ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      F.fprintf fmt.mem "%s\t%s\n" id e_id
  | Cil.Mem e, offset ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      if offset <> Cil.NoOffset then
        pp_offset fmt n lv (Cil.Mem e', Cil.NoOffset) offset mem

and pp_offset fmt n orig_lv lv o mem =
  (* for safeness *)
  let orig_lv_id = Hashtbl.find RelSyntax.lv_map orig_lv in
  pp_lv fmt n lv mem;
  let lv_id = Hashtbl.find RelSyntax.lv_map lv in
  match o with
  | Cil.NoOffset -> ()
  | Cil.Field (f, o') ->
      F.fprintf fmt.field "%s\t%s\n" orig_lv_id lv_id;
      if o' <> Cil.NoOffset then pp_offset fmt n lv (append_field lv f) o' mem
  | Cil.Index (e, o') ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      F.fprintf fmt.index "%s\t%s\t%s\n" orig_lv_id lv_id e_id;
      if o' <> Cil.NoOffset then pp_offset fmt n lv (append_index lv e') o' mem

and pp_exp fmt n e mem =
  let id =
    if Hashtbl.mem RelSyntax.exp_map e then Hashtbl.find RelSyntax.exp_map e
    else RelSyntax.new_exp_id e
  in
  match e with
  | Cil.Const _ -> F.fprintf fmt.const_exp "%s\n" id
  | Cil.Lval lv ->
      pp_lv fmt n lv mem;
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      F.fprintf fmt.lval_exp "%s\t%s\n" id lv_id
  | Cil.BinOp (bop, e1, e2, _) ->
      RelSyntax.pp_binop fmt bop;
      pp_exp fmt n e1 mem;
      pp_exp fmt n e2 mem;
      let e1_id = Hashtbl.find RelSyntax.exp_map e1 in
      let e2_id = Hashtbl.find RelSyntax.exp_map e2 in
      F.fprintf fmt.binop_exp "%s\t%s\t%s\t%s\n" id
        (RelSyntax.string_of_bop bop)
        e1_id e2_id
  | Cil.UnOp (unop, e, _) ->
      pp_exp fmt n e mem;
      RelSyntax.pp_unop fmt unop;
      let e_id = Hashtbl.find RelSyntax.exp_map e in
      F.fprintf fmt.unop_exp "%s\t%s\t%s\n" id
        (RelSyntax.string_of_uop unop)
        e_id
  | Cil.CastE (_, e) ->
      pp_exp fmt n e mem;
      let e_id = Hashtbl.find RelSyntax.exp_map e in
      F.fprintf fmt.cast_exp "%s\t%s\n" id e_id
  | Cil.StartOf l ->
      pp_lv fmt n l mem;
      let l_id = Hashtbl.find RelSyntax.lv_map l in
      F.fprintf fmt.start_of "%s\t%s\n" id l_id;
      if !Options.patron then F.fprintf fmt.lval_exp "%s\t%s\n" id l_id
  | Cil.SizeOfE e1 ->
      pp_exp fmt n e1 mem;
      let e_id = Hashtbl.find RelSyntax.exp_map e1 in
      F.fprintf fmt.sizeof_exp "%s\t%s\n" id e_id
  | Cil.AddrOf l ->
      pp_lv fmt n l mem;
      let l_id = Hashtbl.find RelSyntax.lv_map l in
      F.fprintf fmt.other_exp "%s\t%s\n" id l_id;
      F.fprintf fmt.addr_of "%s\t%s\n" id l_id
  | _ -> F.fprintf fmt.other_exp "%s\n" id

let alloc_target = Str.regexp ".*alloc.*"

let read_target =
  [
    Str.regexp ".*getuint.*";
    Str.regexp ".*getint.*";
    Str.regexp ".*getfloat.*";
    Str.regexp ".*getdouble.*";
    Str.regexp ".*getc.*";
    Str.regexp ".*getuchar.*";
    Str.regexp ".*getchar.*";
    Str.regexp ".*getushort.*";
    Str.regexp ".*getshort.*";
    Str.regexp ".*getulong.*";
    Str.regexp ".*getlong.*";
    Str.regexp ".*getulonglong.*";
    Str.regexp ".*getlonglong.*";
    Str.regexp ".*read.*";
    Str.regexp ".*atoi.*";
    Str.regexp ".*atof.*";
    Str.regexp ".*atol.*";
    Str.regexp ".*atoll.*";
    Str.regexp ".*htonl.*";
    Str.regexp ".*htons.*";
    Str.regexp ".*ntohl.*";
    Str.regexp ".*ntohs.*";
    Str.regexp ".*scanf.*";
  ]

let parse_call_id ?(libcall = false) n e' el' =
  if
    List.exists
      (fun re -> Str.string_match re (CilHelper.s_exp e') 0)
      read_target
  then
    if Hashtbl.mem RelSyntax.readcall_map (n, e', el') then
      Hashtbl.find RelSyntax.readcall_map (n, e', el')
    else RelSyntax.new_readcall_id (n, e', el')
  else if
    Str.string_match alloc_target (CilHelper.s_exp e') 0 && List.length el' > 0
  then
    let size = List.hd el' in
    let alloc = IntraCfg.Cmd.Array size in
    if Hashtbl.mem RelSyntax.alloc_map alloc then
      Hashtbl.find RelSyntax.alloc_map alloc
    else RelSyntax.new_alloc_id alloc
  else if libcall then
    if Hashtbl.mem RelSyntax.libcall_map (n, e', el') then
      Hashtbl.find RelSyntax.libcall_map (n, e', el')
    else RelSyntax.new_libcall_id (n, e', el')
  else if Hashtbl.mem RelSyntax.call_map (n, e', el') then
    Hashtbl.find RelSyntax.call_map (n, e', el')
  else RelSyntax.new_call_id (n, e', el')

let pp_dug_cmd fmt icfg dug n mem =
  let pid = Node.get_pid n in
  if G.pred n dug |> List.length = 2 then
    F.fprintf fmt.RelSyntax.join "%a\n" Node.pp n;
  F.fprintf fmt.func "%s\t%a\n" pid Node.pp n;
  match InterCfg.cmdof icfg n with
  | Cskip _ ->
      if InterCfg.is_entry n then F.fprintf fmt.entry "%a\n" Node.pp n
      else if InterCfg.is_exit n then F.fprintf fmt.exit "%a\n" Node.pp n
      else F.fprintf fmt.skip "%a\n" Node.pp n
  | Cset (lv, e, _) ->
      pp_lv fmt n lv mem;
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id e_id;
      F.fprintf fmt.assign "%a\t%s\t%s\n" Node.pp n lv_id e_id
  | Cexternal (_, _) -> F.fprintf fmt.cmd "external\n"
  | Calloc (lv, (Array e as alloc), _, _, _) ->
      pp_lv fmt n lv mem;
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let size_e_id = Hashtbl.find RelSyntax.exp_map e' in
      let alloc_id =
        if Hashtbl.mem RelSyntax.alloc_map alloc then
          Hashtbl.find RelSyntax.alloc_map alloc
        else RelSyntax.new_alloc_id alloc
      in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id alloc_id;
      F.fprintf fmt.alloc_exp "%s\t%s\n" alloc_id size_e_id;
      F.fprintf fmt.alloc "%a\t%s\t%s\n" Node.pp n lv_id size_e_id
  | Calloc (_, _, _, _, _) -> F.fprintf fmt.cmd "alloc\n"
  | Csalloc (lv, str, _) ->
      pp_lv fmt n lv mem;
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let salloc_id =
        if Hashtbl.mem RelSyntax.salloc_map str then
          Hashtbl.find RelSyntax.salloc_map str
        else RelSyntax.new_salloc_id str
      in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id salloc_id;
      F.fprintf fmt.salloc_exp "%s\t%s\n" salloc_id str;
      F.fprintf fmt.salloc "%a\t%s\n" Node.pp n lv_id
  | Cfalloc (_, _, _) -> F.fprintf fmt.cmd "falloc\n"
  | Ccall (lv_opt, (Lval (Var f, NoOffset) as e), el, _)
    when f.vstorage = Cil.Extern ->
      let lv =
        if Option.is_none lv_opt then RelSyntax.donotcare_lv
        else Option.get lv_opt
      in
      pp_lv fmt n lv mem;
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let el' =
        List.map
          (fun e -> if !Options.remove_cast then RelSyntax.remove_cast e else e)
          el
      in
      List.iter (fun e -> pp_exp fmt n e mem) el';
      let arg_id = RelSyntax.pp_arg fmt el' in
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      let libcall_id = parse_call_id ~libcall:true n e' el' in
      if Str.string_match (Str.regexp "Read.*") libcall_id 0 then
        F.fprintf fmt.readcall_exp "%s\t%s\t%s\n" libcall_id e_id arg_id
      else if Str.string_match (Str.regexp "Alloc.*") libcall_id 0 then
        let size = List.hd el' in
        let size_id = Hashtbl.find RelSyntax.exp_map size in
        F.fprintf fmt.alloc_exp "%s\t%s\n" libcall_id size_id
      else F.fprintf fmt.libcall_exp "%s\t%s\t%s\n" libcall_id e_id arg_id;
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id libcall_id;
      F.fprintf fmt.libcall "%a\t%s\t%s\t%s\n" Node.pp n lv_id e_id arg_id
  | Ccall (lv_opt, e, el, _) ->
      let lv =
        if Option.is_none lv_opt then RelSyntax.donotcare_lv
        else Option.get lv_opt
      in
      pp_lv fmt n lv mem;
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let el' =
        List.map
          (fun e -> if !Options.remove_cast then RelSyntax.remove_cast e else e)
          el
      in
      List.iter (fun e -> pp_exp fmt n e mem) el';
      let arg_id = RelSyntax.pp_arg fmt el' in
      let lv_id = Hashtbl.find RelSyntax.lv_map lv in
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      let call_id = parse_call_id n e' el' in
      if Str.string_match (Str.regexp "Read.*") call_id 0 then
        F.fprintf fmt.readcall_exp "%s\t%s\t%s\n" call_id e_id arg_id
      else if Str.string_match (Str.regexp "Alloc.*") call_id 0 then
        let size = List.hd el' in
        let size_id = Hashtbl.find RelSyntax.exp_map size in
        F.fprintf fmt.alloc_exp "%s\t%s\n" call_id size_id
      else F.fprintf fmt.call_exp "%s\t%s\t%s\n" call_id e_id arg_id;
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id call_id;
      F.fprintf fmt.call "%a\t%s\t%s\t%s\n" Node.pp n lv_id e_id arg_id
  | Creturn (Some e, _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let id = Hashtbl.find RelSyntax.exp_map e' in
      F.fprintf fmt.return "%a\t%s\n" Node.pp n id
  | Cassume (e, _, _) ->
      let e' = if !Options.remove_cast then RelSyntax.remove_cast e else e in
      pp_exp fmt n e' mem;
      let e_id = Hashtbl.find RelSyntax.exp_map e' in
      F.fprintf fmt.assume "%a\t%s\n" Node.pp n e_id
  | _ -> F.fprintf fmt.cmd "unknown"

let print_patron_relation dirname icfg dug mem =
  let fmt, channels = RelSyntax.make_formatters dirname in
  G.iter_node (fun n -> pp_dug_cmd fmt icfg dug n mem) dug;
  RelSyntax.close_formatters fmt channels

let print_raw_patron dirname =
  let oc_exp_json = open_out (dirname ^ "/Exp.json") in
  let oc_exp_text = open_out (dirname ^ "/Exp.map") in
  let oc_lval_text = open_out (dirname ^ "/Lval.map") in
  let exp_fmt = F.formatter_of_out_channel oc_exp_text in
  let lval_fmt = F.formatter_of_out_channel oc_lval_text in
  let l =
    Hashtbl.fold
      (fun exp id l ->
        F.fprintf exp_fmt "%s\t%s\n" id (CilHelper.s_exp exp);
        let json_exp = CilJson.of_exp exp in
        let exp =
          `Assoc
            [
              ("tree", json_exp);
              ("text", `String (CilHelper.s_exp exp));
              ("abs_text", `String (RelSyntax.string_of_abstract_exp exp));
            ]
        in
        (id, exp) :: l)
      RelSyntax.exp_map []
  in
  let json = `Assoc l in
  Yojson.Safe.to_channel oc_exp_json json;
  Hashtbl.iter
    (fun lv id -> F.fprintf lval_fmt "%s\t%s\n" id (CilHelper.s_lv lv))
    RelSyntax.lv_map;
  F.pp_print_flush exp_fmt ();
  F.pp_print_flush lval_fmt ();
  close_out oc_exp_json;
  close_out oc_exp_text;
  close_out oc_lval_text

let print_fact_patron dirname icfg dug mem =
  Hashtbl.reset RelSyntax.exp_map;
  Hashtbl.reset RelSyntax.lv_map;
  Hashtbl.reset RelSyntax.binop_map;
  Hashtbl.reset RelSyntax.unop_map;
  print_patron_relation dirname icfg dug mem;
  print_raw_patron dirname

module AexpSet = BatSet.Make (struct
  type t = AlarmExp.t

  let compare = compare
end)

let print_raw_alarm dirname =
  let oc_alarm = open_out (dirname ^ "/Alarm.map") in
  let fmt = F.formatter_of_out_channel oc_alarm in
  Hashtbl.iter
    (fun aexp id ->
      F.fprintf fmt "%s\t%s\t%s\n"
        (AlarmExp.location_of aexp |> CilHelper.s_location)
        (AlarmExp.to_string aexp) id)
    alarm_exp_map;
  F.pp_print_flush fmt ();
  close_out oc_alarm

let print_patron analysis global dug alarms =
  (* for patern to use Loc relation, print_patron uses DUG instead *)
  let dug = G.copy dug in
  let alarms = Report.get alarms Report.UnProven in
  let print_for_one_alarm dug (i, visited) alarm =
    let alarm_loc = alarm.Report.loc |> CilHelper.s_location in
    if
      !Options.target_loc = []
      || List.exists (fun loc -> loc = alarm_loc) !Options.target_loc
    then (
      let dug = G.copy dug in
      let aexp = alarm.Report.exp in
      (if AexpSet.mem aexp visited |> not then
         let alarms = [ alarm ] in
         let dug = optimize ~verbose:false alarms dug in
         if G.mem_node alarm.Report.node dug then (
           let dirname =
             F.sprintf "%s/datalog/%d" (FileManager.analysis_dir analysis) i
           in
           FileManager.mkdir dirname;
           print_fact_patron dirname global.Global.icfg dug global.mem;
           print_taint_alarm_in_dir dirname alarms;
           print_sems dirname dug));
      G.clear dug;
      (i + 1, AexpSet.add aexp visited))
    else (i, visited)
  in
  List.fold_left (print_for_one_alarm dug) (0, AexpSet.empty) alarms |> ignore;
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  print_raw_alarm dirname
