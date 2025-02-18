(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)

open Vocab
open Global
open BasicDom
open ArrayBlk
open OctDom
open AlarmExp
open Report

let analysis = Spec.Octagon

module Analysis = SparseAnalysis.MakeWithAccess (OctSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module Mem = OctDom.Mem

let string_of_alarminfo offset size diff =
  "offset: " ^ Itv.to_string offset ^ ", size: " ^ Itv.to_string size
  ^ ", size - offset: " ^ Itv.to_string diff

let check packconf pid v1 v2opt v2exp ptrmem mem =
  let arr = ItvDom.Val.array_of_val v1 in
  if ArrayBlk.eq arr ArrayBlk.bot || ArrayBlk.cardinal arr > 1 then
    ItvAnalysis.check_bo v1 v2opt
  else
    ArrayBlk.foldi
      (fun a arr lst ->
        let offset_idx =
          match v2opt with
          | None -> arr.ArrInfo.offset
          | Some v2 -> Itv.plus arr.ArrInfo.offset (ItvDom.Val.itv_of_val v2)
        in
        let diff =
          match v2exp with
          | None -> Itv.minus arr.ArrInfo.size offset_idx
          | Some e ->
              OctSem.check_bo pid packconf a arr.ArrInfo.offset e ptrmem mem
        in
        let status =
          if Itv.is_bot offset_idx || Itv.is_bot arr.ArrInfo.size then BotAlarm
            (* proven by interval *)
          else if
            try
              Itv.lower offset_idx >= 0
              && Itv.upper offset_idx < Itv.lower arr.ArrInfo.size
            with _ -> false
          then Proven (* proven by octagon *)
          else if
            try
              Itv.lower offset_idx >= 0
              && Itv.lower arr.ArrInfo.size > 0
              && Itv.lower diff >= 1
            with _ -> false
          then Proven
          else UnProven
        in
        (status, Some a, string_of_alarminfo offset_idx arr.ArrInfo.size diff)
        :: lst)
      arr []

let inspect_aexp packconf node aexp ptrmem mem queries =
  let pid = InterCfg.Node.pid node in
  if !Options.oct_debug then (
    prerr_endline "query";
    prerr_endline (AlarmExp.to_string aexp));
  (match aexp with
  | ArrayExp (lv, e, loc) ->
      let v1 =
        ItvDom.Mem.lookup
          (ItvSem.eval_lv (InterCfg.Node.pid node) lv ptrmem)
          ptrmem
      in
      let v2 = ItvSem.eval (InterCfg.Node.pid node) e ptrmem in
      check packconf pid v1 (Some v2) (Some e) ptrmem mem
      |> List.map (fun (status, a, desc) ->
             { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
  | DerefExp (Cil.BinOp (op, e1, e2, _), loc)
    when op = Cil.PlusPI || op = Cil.IndexPI ->
      let v1 = ItvSem.eval (InterCfg.Node.pid node) e1 ptrmem in
      let v2 = ItvSem.eval (InterCfg.Node.pid node) e2 ptrmem in
      check packconf pid v1 (Some v2) (Some e2) ptrmem mem
      |> List.map (fun (status, a, desc) ->
             { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
  | DerefExp (e, loc) ->
      let v = ItvSem.eval (InterCfg.Node.pid node) e ptrmem in
      check packconf pid v None None ptrmem mem
      |> cond
           (ItvDom.Val.eq ItvDom.Val.bot v)
           (List.map (fun (status, a, desc) ->
                {
                  node;
                  exp = aexp;
                  loc;
                  allocsite = a;
                  status;
                  desc;
                  src = None;
                }))
           (List.map (fun (status, a, desc) ->
                if status = Report.BotAlarm then
                  {
                    node;
                    exp = aexp;
                    loc;
                    allocsite = a;
                    status = Proven;
                    desc = "valid pointer dereference";
                    src = None;
                  }
                else
                  {
                    node;
                    exp = aexp;
                    loc;
                    allocsite = a;
                    status;
                    desc;
                    src = None;
                  }))
  | Strcpy (e1, e2, loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.pid node) e1 ptrmem in
      let v2 = ItvSem.eval (InterCfg.Node.pid node) e2 ptrmem in
      let v2 =
        ItvDom.Val.of_itv (ArrayBlk.nullof (ItvDom.Val.array_of_val v2))
      in
      check packconf pid v1 (Some v2) None ptrmem mem
      |> List.map (fun (status, a, desc) ->
             { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
  | Strcat (e1, e2, loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.pid node) e1 ptrmem in
      let v2 = ItvSem.eval (InterCfg.Node.pid node) e2 ptrmem in
      let np1 = ArrayBlk.nullof (ItvDom.Val.array_of_val v1) in
      let np2 = ArrayBlk.nullof (ItvDom.Val.array_of_val v2) in
      let np = ItvDom.Val.of_itv (Itv.plus np1 np2) in
      check packconf pid v1 (Some np) None ptrmem mem
      |> List.map (fun (status, a, desc) ->
             { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
  | Strncpy (e1, e2, e3, loc)
  | Memcpy (e1, e2, e3, loc)
  | Memmove (e1, e2, e3, loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.pid node) e1 ptrmem in
      let v2 = ItvSem.eval (InterCfg.Node.pid node) e2 ptrmem in
      let e3_1 = Cil.BinOp (Cil.MinusA, e3, Cil.mone, Cil.intType) in
      let v3 = ItvSem.eval (InterCfg.Node.pid node) e3_1 ptrmem in
      let lst1 = check packconf pid v1 (Some v3) (Some e3) ptrmem mem in
      let lst2 = check packconf pid v2 (Some v3) (Some e2) ptrmem mem in
      lst1 @ lst2
      |> List.map (fun (status, a, desc) ->
             { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
  | _ -> [])
  @ queries

let inspect_alarm global spec inputof =
  let nodes = InterCfg.nodes_of global.icfg in
  let total = List.length nodes in
  list_fold
    (fun node (qs, k) ->
      prerr_progressbar ~itv:1000 k total;
      let ptrmem = ItvDom.Table.find node spec.Spec.ptrinfo in
      let mem = Table.find node inputof in
      let cmd = InterCfg.cmd_of global.icfg node in
      let aexps = AlarmExp.collect analysis cmd in
      let qs =
        list_fold
          (fun aexp ->
            if ptrmem = ItvDom.Mem.bot then id (* dead code *)
            else inspect_aexp spec.Spec.locset node aexp ptrmem mem)
          aexps qs
      in
      (qs, k + 1))
    nodes ([], 0)
  |> fst

(* x = y *)
let sparrow_relation_set pid mem exps rel =
  match exps with
  | Cil.Lval x :: Cil.Lval y :: _ ->
      let lv_x = ItvSem.eval_lv pid x mem in
      let lv_y = ItvSem.eval_lv pid y mem in
      PowLoc.fold
        (fun x ->
          PowLoc.fold
            (fun y ->
              OctImpactDom.Relation.add_edge (OctLoc.of_loc x) (OctLoc.of_loc y))
            lv_y)
        lv_x rel
  | _ -> rel

(* x = malloc(y) *)
let sparrow_relation_malloc pid mem exps rel =
  match exps with
  | x :: Cil.Lval y :: _ ->
      let lv_x = ItvSem.eval pid x mem |> ItvDom.Val.allocsites_of_val in
      let lv_y = ItvSem.eval_lv pid y mem in
      BatSet.fold
        (fun x ->
          PowLoc.fold
            (fun y ->
              OctImpactDom.Relation.add_edge (OctLoc.of_size x)
                (OctLoc.of_loc y))
            lv_y)
        lv_x rel
  | _ -> rel

(* x = strlen(y) *)
let sparrow_relation_strlen pid mem exps rel =
  match exps with
  | Cil.Lval x :: y :: _ ->
      let lv_x = ItvSem.eval_lv pid x mem in
      let lv_y = ItvSem.eval pid y mem |> ItvDom.Val.allocsites_of_val in
      PowLoc.fold
        (fun x ->
          BatSet.fold
            (fun y ->
              OctImpactDom.Relation.add_edge (OctLoc.of_loc x)
                (OctLoc.of_size y))
            lv_y)
        lv_x rel
  | _ -> rel

let manual_packing (global, itvinputof) =
  let nodes = InterCfg.nodes_of global.icfg in
  list_fold
    (fun n a ->
      let mem = ItvDom.Table.find n itvinputof in
      let pid = InterCfg.Node.pid n in
      match InterCfg.cmd_of global.icfg n with
      | IntraCfg.Cmd.Ccall (None, Cil.Lval (Cil.Var f, Cil.NoOffset), exps, _)
        ->
          if f.vname = "sparrow_relation_set" then
            sparrow_relation_set pid mem exps a
          else if f.vname = "sparrow_relation_malloc" then
            sparrow_relation_malloc pid mem exps a
          else if f.vname = "sparrow_relation_strlen" then
            sparrow_relation_strlen pid mem exps a
          else a
      | _ -> a)
    nodes OctImpactDom.Relation.empty
  |> OctImpactDom.Relation.get_packconf |> PackConf.make itvinputof

(* ********** *
 * Marshaling *
 * ********** *)
let marshal_in global =
  let filename = Filename.basename global.file.fileName in
  let global = MarshalManager.input (filename ^ ".oct.global") in
  let dug = MarshalManager.input (filename ^ ".oct.dug") in
  let input = MarshalManager.input (filename ^ ".oct.input") in
  let output = MarshalManager.input (filename ^ ".oct.output") in
  (global, dug, input, output)

let marshal_out (global, dug, input, output) =
  let filename = Filename.basename global.file.fileName in
  MarshalManager.output (filename ^ ".oct.global") global;
  MarshalManager.output (filename ^ ".oct.dug") dug;
  MarshalManager.output (filename ^ ".oct.input") input;
  MarshalManager.output (filename ^ ".oct.output") output;
  (global, dug, input, output)

let do_analysis (global, itvinputof) =
  let global = { global with table = itvinputof } in
  let packconf =
    StepManager.stepf_switch false "Compute Packing Configuration"
      [
        (!Options.pack_manual, manual_packing);
        (!Options.pack_impact, OctImpactAnalysis.packing);
      ]
      (global, itvinputof)
  in
  PackConf.print_info packconf;
  let spec =
    {
      Spec.empty with
      analysis;
      locset = packconf;
      locset_fs = packconf;
      ptrinfo = itvinputof;
      premem = Mem.top packconf;
    }
  in
  let dug = Analysis.generate_dug spec global in
  (if !Options.marshal_in then marshal_in global
  else Analysis.perform spec global dug)
  |> opt !Options.marshal_out marshal_out
  |> StepManager.stepf true "Generate Alarm Report"
       (fun (global, _, inputof, outputof) ->
         (global, inputof, outputof, inspect_alarm global spec inputof))
