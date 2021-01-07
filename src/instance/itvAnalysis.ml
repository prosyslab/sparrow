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

open Cil
open Global
open BasicDom
open Vocab
open ItvDom
open ArrayBlk
open AlarmExp
open Report
module L = Logging
module F = Format

let analysis = Spec.Interval

module Analysis = SparseAnalysis.Make (ItvSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module DUGraph = Analysis.DUGraph
module Node = InterCfg.Node

let print_abslocs_info locs =
  let lvars = BatSet.filter Loc.is_lvar locs in
  let gvars = BatSet.filter Loc.is_gvar locs in
  let allocsites = BatSet.filter Loc.is_allocsite locs in
  let fields = BatSet.filter Loc.is_field locs in
  prerr_endline ("#abslocs    : " ^ i2s (BatSet.cardinal locs));
  prerr_endline ("#lvars      : " ^ i2s (BatSet.cardinal lvars));
  prerr_endline ("#gvars      : " ^ i2s (BatSet.cardinal gvars));
  prerr_endline ("#allocsites : " ^ i2s (BatSet.cardinal allocsites));
  prerr_endline ("#fields     : " ^ i2s (BatSet.cardinal fields))

(* **************** *
 * Alarm Inspection *
 * **************** *)
let ignore_alarm a arr offset =
  !Options.bugfinder >= 1
  && ( Allocsite.is_string_allocsite a
     || arr.ArrInfo.size = Itv.top || arr.ArrInfo.size = Itv.one
     || (offset = Itv.top && arr.ArrInfo.size = Itv.nat)
     || offset = Itv.zero )
  || (!Options.bugfinder >= 2 && not (Itv.is_const arr.ArrInfo.size))
  || !Options.bugfinder >= 3
     && ( offset = Itv.top
        || Itv.meet arr.ArrInfo.size Itv.zero <> Itv.bot
        || (offset = Itv.top && arr.ArrInfo.offset <> Itv.top) )

let check_bo v1 v2opt =
  let arr = Val.array_of_val v1 in
  if ArrayBlk.eq arr ArrayBlk.bot then [ (BotAlarm, None, "Array is Bot") ]
  else
    ArrayBlk.foldi
      (fun a arr lst ->
        let offset =
          match v2opt with
          | None -> arr.ArrInfo.offset
          | Some v2 -> Itv.plus arr.ArrInfo.offset (Val.itv_of_val v2)
        in
        let status =
          try
            if Itv.is_bot offset || Itv.is_bot arr.ArrInfo.size then BotAlarm
            else if ignore_alarm a arr offset then Proven
            else
              let ol, ou = (Itv.lower offset, Itv.upper offset) in
              let sl = Itv.lower arr.ArrInfo.size in
              if ou >= sl || ol < 0 then UnProven else Proven
          with _ -> UnProven
        in
        (status, Some a, string_of_alarminfo offset arr.ArrInfo.size) :: lst)
      arr []

let check_nd v1 =
  let ploc = Val.pow_loc_of_val v1 in
  if PowLoc.eq ploc PowLoc.bot then [ (BotAlarm, None, "PowLoc is Bot") ]
  else if PowLoc.mem Loc.null ploc then [ (UnProven, None, "Null Dereference") ]
  else [ (Proven, None, "") ]

let inspect_aexp_bo node aexp mem queries =
  ( match aexp with
  | ArrayExp (lv, e, loc) ->
      let v1 =
        Mem.lookup (ItvSem.eval_lv (InterCfg.Node.get_pid node) lv mem) mem
      in
      let v2 = ItvSem.eval (InterCfg.Node.get_pid node) e mem in
      let lst = check_bo v1 (Some v2) in
      List.map
        (fun (status, a, desc) ->
          { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
        lst
  | DerefExp (e, loc) ->
      let v = ItvSem.eval (InterCfg.Node.get_pid node) e mem in
      let lst = check_bo v None in
      if Val.eq Val.bot v then
        List.map
          (fun (status, a, desc) ->
            { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
          lst
      else
        List.map
          (fun (status, a, desc) ->
            if status = BotAlarm then
              {
                node;
                exp = aexp;
                loc;
                status = Proven;
                allocsite = a;
                desc = "valid pointer dereference";
                src = None;
              }
            else
              { node; exp = aexp; loc; status; allocsite = a; desc; src = None })
          lst
  | Strcpy (e1, e2, loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.get_pid node) e1 mem in
      let v2 = ItvSem.eval (InterCfg.Node.get_pid node) e2 mem in
      let v2 = Val.of_itv (ArrayBlk.nullof (Val.array_of_val v2)) in
      let lst = check_bo v1 (Some v2) in
      List.map
        (fun (status, a, desc) ->
          { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
        lst
  | Strcat (e1, e2, loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.get_pid node) e1 mem in
      let v2 = ItvSem.eval (InterCfg.Node.get_pid node) e2 mem in
      let np1 = ArrayBlk.nullof (Val.array_of_val v1) in
      let np2 = ArrayBlk.nullof (Val.array_of_val v2) in
      let np = Val.of_itv (Itv.plus np1 np2) in
      let lst = check_bo v1 (Some np) in
      List.map
        (fun (status, a, desc) ->
          { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
        lst
  | Strncpy (e1, e2, e3, loc)
  | Memcpy (e1, e2, e3, loc)
  | Memmove (e1, e2, e3, loc)
  | BufferOverrunLib ("strncmp", [ e1; e2; e3 ], loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.get_pid node) e1 mem in
      let v2 = ItvSem.eval (InterCfg.Node.get_pid node) e2 mem in
      let e3_1 = Cil.BinOp (Cil.MinusA, e3, Cil.one, Cil.intType) in
      let v3 = ItvSem.eval (InterCfg.Node.get_pid node) e3_1 mem in
      let lst1 = check_bo v1 (Some v3) in
      let lst2 = check_bo v2 (Some v3) in
      List.map
        (fun (status, a, desc) ->
          { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
        (lst1 @ lst2)
  | BufferOverrunLib ("memchr", [ e1; _; e3 ], loc) ->
      let v1 = ItvSem.eval (InterCfg.Node.get_pid node) e1 mem in
      let e3_1 = Cil.BinOp (Cil.MinusA, e3, Cil.one, Cil.intType) in
      let v3 = ItvSem.eval (InterCfg.Node.get_pid node) e3_1 mem in
      let lst1 = check_bo v1 (Some v3) in
      List.map
        (fun (status, a, desc) ->
          { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
        lst1
  | _ -> [] )
  @ queries

let inspect_aexp_nd node aexp mem queries =
  ( match aexp with
  | DerefExp (e, loc) ->
      let v = ItvSem.eval (InterCfg.Node.get_pid node) e mem in
      let lst = check_nd v in
      if Val.eq Val.bot v then
        List.map
          (fun (status, a, desc) ->
            { node; exp = aexp; loc; allocsite = a; status; desc; src = None })
          lst
      else
        List.map
          (fun (status, a, desc) ->
            if status = BotAlarm then
              {
                node;
                exp = aexp;
                loc;
                status = Proven;
                allocsite = a;
                desc = "valid pointer dereference";
                src = None;
              }
            else
              { node; exp = aexp; loc; status; allocsite = a; desc; src = None })
          lst
  | _ -> [] )
  @ queries

let check_dz v =
  let v = Val.itv_of_val v in
  if Itv.le Itv.zero v then [ (UnProven, None, "Divide by " ^ Itv.to_string v) ]
  else [ (Proven, None, "") ]

let inspect_aexp_dz node aexp mem queries =
  ( match aexp with
  | DivExp (_, e, loc) ->
      let v = ItvSem.eval (InterCfg.Node.get_pid node) e mem in
      let lst = check_dz v in
      List.map
        (fun (status, _, desc) ->
          { node; exp = aexp; loc; allocsite = None; status; desc; src = None })
        lst
  | _ -> [] )
  @ queries

let machine_gen_code q =
  (* yacc-generated code *)
  Filename.check_suffix q.loc.Cil.file ".y"
  || Filename.check_suffix q.loc.Cil.file ".yy.c"
  || Filename.check_suffix q.loc.Cil.file ".simple"
  || (* sparrow-generated code *)
  InterCfg.Node.get_pid q.node = InterCfg.global_proc

let rec unsound_exp = function
  | Cil.BinOp (Cil.PlusPI, Cil.Lval (Cil.Mem _, _), _, _) -> true
  | Cil.BinOp (b, _, _, _)
    when b = Mod || b = Cil.Shiftlt || b = Shiftrt || b = BAnd || b = BOr
         || b = BXor || b = LAnd || b = LOr ->
      true
  | Cil.BinOp (bop, Cil.Lval (Cil.Var _, _), Cil.Lval (Cil.Var _, _), _)
    when bop = Cil.PlusA || bop = Cil.MinusA ->
      true
  | Cil.BinOp (_, e1, e2, _) -> unsound_exp e1 || unsound_exp e2
  | Cil.CastE (_, e) -> unsound_exp e
  | Cil.Lval lv -> unsound_lv lv
  | _ -> false

and unsound_lv = function
  | _, Cil.Index _ -> true
  | Cil.Var v, _ -> is_global_integer v || is_union v.vtype || is_temp_integer v
  | Cil.Mem _, Cil.NoOffset -> true
  | _, _ -> false

and is_global_integer v = v.vglob && Cil.isIntegralType v.vtype

and is_union typ =
  match Cil.unrollTypeDeep typ with
  | Cil.TPtr (Cil.TComp (c, _), _) -> not c.cstruct
  | _ -> false

and is_temp_integer v =
  !Options.bugfinder >= 2
  && (try String.sub v.vname 0 3 = "tmp" with _ -> false)
  && Cil.isIntegralType v.vtype

let unsound_aexp = function
  | ArrayExp (_, e, _) -> unsound_exp e
  | DerefExp (e, _) -> unsound_exp e
  | _ -> false

let formal_param global q =
  let cfg = InterCfg.cfgof global.icfg (InterCfg.Node.get_pid q.node) in
  let formals = IntraCfg.get_formals cfg |> List.map (fun x -> x.Cil.vname) in
  let rec find_exp = function
    | Cil.BinOp (_, e1, e2, _) -> find_exp e1 || find_exp e2
    | Cil.CastE (_, e) -> find_exp e
    | Cil.Lval lv -> find_lv lv
    | _ -> false
  and find_lv = function
    | Cil.Var v, _ -> List.mem v.vname formals && Cil.isIntegralType v.vtype
    | _, _ -> false
  in
  match q.exp with
  | ArrayExp (_, e, _) | DerefExp (e, _) -> find_exp e
  | _ -> false

let unsound_filter _ ql =
  let filtered =
    List.filter
      (fun q ->
        (not (machine_gen_code q)) && not (unsound_aexp q.exp)
        (*     not (formal_param global q)*))
      ql
  in
  let partition =
    list_fold
      (fun q m ->
        let p_als = try BatMap.find (q.loc, q.node) m with _ -> [] in
        BatMap.add (q.loc, q.node) (q :: p_als) m)
      filtered BatMap.empty
  in
  BatMap.fold
    (fun ql result ->
      if List.length (Report.get ql UnProven) > 3 then
        List.map (fun q -> { q with status = Proven }) ql @ result
      else ql @ result)
    partition []

let filter qs s = List.filter (fun q -> q.status = s) qs

let generate (global, inputof, target) =
  let nodes = InterCfg.nodesof global.icfg in
  let total = List.length nodes in
  list_fold
    (fun node (qs, k) ->
      prerr_progressbar ~itv:1000 k total;
      let mem = Table.find node inputof in
      let cmd = InterCfg.cmdof global.icfg node in
      let aexps = AlarmExp.collect analysis cmd in
      let qs =
        list_fold
          (fun aexp ->
            if mem = Mem.bot then id (* dead code *)
            else
              match target with
              | BO -> inspect_aexp_bo node aexp mem
              | ND -> inspect_aexp_nd node aexp mem
              | DZ -> inspect_aexp_dz node aexp mem)
          aexps qs
      in
      (qs, k + 1))
    nodes ([], 0)
  |> fst
  |> opt (!Options.bugfinder > 0) (unsound_filter global)

let generate_with_mem (global, mem, target) =
  let nodes = InterCfg.nodesof global.icfg in
  list_fold
    (fun node ->
      let cmd = InterCfg.cmdof global.icfg node in
      let aexps = AlarmExp.collect analysis cmd in
      if mem = Mem.bot then id (* dead code *)
      else
        match target with
        | BO -> list_fold (fun aexp -> inspect_aexp_bo node aexp mem) aexps
        | ND -> list_fold (fun aexp -> inspect_aexp_nd node aexp mem) aexps
        | DZ -> list_fold (fun aexp -> inspect_aexp_dz node aexp mem) aexps)
    nodes []

(* ********** *
 * Marshaling *
 * ********** *)
let marshal_in global =
  let filename = Filename.basename global.file.fileName in
  let global = MarshalManager.input (filename ^ ".itv.global") in
  let dug = MarshalManager.input (filename ^ ".itv.dug") in
  let input = MarshalManager.input (filename ^ ".itv.input") in
  let output = MarshalManager.input (filename ^ ".itv.output") in
  (global, dug, input, output)

let marshal_out (global, dug, input, output) =
  let filename = Filename.basename global.file.fileName in
  MarshalManager.output (filename ^ ".itv.global") global;
  MarshalManager.output (filename ^ ".itv.dug") dug;
  MarshalManager.output (filename ^ ".itv.input") input;
  MarshalManager.output (filename ^ ".itv.output") output;
  (global, dug, input, output)

let inspect_alarm global _ inputof =
  (if !Options.bo then generate (global, inputof, Report.BO) else [])
  @ (if !Options.nd then generate (global, inputof, Report.ND) else [])
  @ if !Options.dz then generate (global, inputof, Report.DZ) else []

let get_locset mem =
  ItvDom.Mem.foldi
    (fun l v locset ->
      locset |> PowLoc.add l
      |> PowLoc.union (Val.pow_loc_of_val v)
      |> BatSet.fold
           (fun a -> PowLoc.add (Loc.of_allocsite a))
           (Val.allocsites_of_val v))
    mem PowLoc.empty

module LMap = BatMap.Make (Loc)
module NMap = BatMap.Make (Node)

(* connect InterCfg.start_node to nodes that do not have predecessors *)
let connect_from_start g =
  DUGraph.fold_node
    (fun node l ->
      if DUGraph.pred node g = [] && node <> InterCfg.start_node then node :: l
      else l)
    g []
  |> List.fold_left (fun g n -> DUGraph.add_edge InterCfg.start_node n g) g

let print_datalog_fact _ global dug alarms =
  let dug = connect_from_start dug in
  let alarms =
    List.rev_map
      (fun q -> { q with src = Some (InterCfg.start_node, Cil.locUnknown) })
      alarms
  in
  RelSyntax.print analysis global.icfg;
  Provenance.print analysis global.relations;
  RelDUGraph.print analysis global dug alarms;
  RelDUGraph.print_alarm analysis alarms

let ignore_file file =
  BatSet.elements !Options.filter_file
  |> List.map (fun str -> Str.regexp (".*" ^ str ^ ".*"))
  |> List.exists (fun re -> Str.string_match re file 0)

let ignore_node node =
  BatSet.elements !Options.filter_node
  |> List.map Str.regexp
  |> List.exists (fun re ->
         Str.string_match re (InterCfg.Node.to_string node) 0)

let ignore_function node =
  BatSet.elements !Options.filter_function
  |> List.map Str.regexp
  |> List.exists (fun re -> Str.string_match re (InterCfg.Node.get_pid node) 0)

let ignore_allocsite allocsite =
  BatSet.elements !Options.filter_allocsite
  |> List.map (fun str -> Str.regexp (".*" ^ str ^ ".*"))
  |> List.exists (fun re -> Str.string_match re allocsite 0)

let post_process spec (global, dug, inputof, outputof) =
  let alarms =
    StepManager.stepf true "Generate Alarm Report"
      (inspect_alarm global spec)
      inputof
    |> List.filter (fun q ->
           match q.Report.allocsite with
           | Some a -> not (ignore_allocsite (Allocsite.to_string a))
           | None -> true)
    |> List.filter (fun a -> not (ignore_file a.Report.loc.file))
    |> List.filter (fun a -> not (ignore_function a.Report.node))
    |> List.filter (fun a -> not (ignore_node a.Report.node))
  in
  let report_file =
    open_out (FileManager.analysis_dir analysis ^ "/report.txt")
  in
  let fmt = F.formatter_of_out_channel report_file in
  Report.print ~fmt:(Some fmt) global alarms;
  close_out report_file;
  if !Options.extract_datalog_fact then
    print_datalog_fact spec global dug alarms;
  (global, dug, inputof, outputof, alarms)

let stat locset =
  let gvar, lvar, allocsite, field =
    PowLoc.fold
      (fun loc (gvar, lvar, allocsite, field) ->
        if Loc.is_gvar loc then (gvar + 1, lvar, allocsite, field)
        else if Loc.is_lvar loc then (gvar, lvar + 1, allocsite, field)
        else if Loc.is_allocsite loc then (gvar, lvar, allocsite + 1, field)
        else (gvar, lvar, allocsite + 1, field + 1))
      locset (0, 0, 0, 0)
  in
  let cardinal = PowLoc.cardinal locset |> float_of_int in
  L.info ~level:1 "#global variables = %d (%.1f%%)\n" gvar
    (float_of_int gvar /. cardinal *. 100.0);
  L.info ~level:1 "#local variables  = %d (%.1f%%)\n" lvar
    (float_of_int lvar /. cardinal *. 100.0);
  L.info ~level:1 "#allocsite        = %d (%.1f%%)\n" allocsite
    (float_of_int allocsite /. cardinal *. 100.0);
  L.info ~level:1 "#fields           = %d (%.1f%%)\n" field
    (float_of_int field /. cardinal *. 100.0)

let do_analysis global =
  let _ = prerr_memory_usage () in
  let locset = get_locset global.mem in
  let locset_fs = PartialFlowSensitivity.select global locset in
  let unsound_lib = UnsoundLib.collect global in
  let unsound_update = !Options.bugfinder >= 2 in
  let unsound_bitwise = !Options.bugfinder >= 1 in
  let spec =
    {
      Spec.empty with
      analysis;
      locset;
      locset_fs;
      premem = global.mem;
      unsound_lib;
      unsound_update;
      unsound_bitwise;
    }
  in
  stat locset;
  cond !Options.marshal_in marshal_in (Analysis.perform spec) global
  |> opt !Options.marshal_out marshal_out
  |> post_process spec
