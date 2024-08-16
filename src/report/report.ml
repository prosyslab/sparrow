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
open BasicDom
open ProsysCil
open Cil
module F = Format
module L = Logging

type target = BO | ND | DZ | IO

type status = Proven | UnProven | BotAlarm

type part_unit = Cil.location

let status_to_string = function
  | Proven -> "Proven"
  | UnProven -> "UnProven"
  | _ -> "BotAlarm"

type query = {
  node : InterCfg.node;
  exp : AlarmExp.t;
  loc : Cil.location;
  allocsite : Allocsite.t option;
  src : (InterCfg.node * Cil.location) option;
  status : status;
  desc : string;
}

let is_unproven q = q.status = UnProven

let get_pid q = InterCfg.Node.get_pid q.node

let get qs status = List.filter (fun q -> q.status = status) qs

let string_of_alarminfo offset size =
  "offset: " ^ Itv.to_string offset ^ ", size: " ^ Itv.to_string size

let partition queries =
  list_fold
    (fun q m ->
      let p_als = try BatMap.find q.loc m with _ -> [] in
      BatMap.add q.loc (q :: p_als) m)
    queries BatMap.empty

let sort_queries queries =
  List.sort
    (fun a b ->
      if Stdlib.compare a.loc.file b.loc.file = 0 then
        if Stdlib.compare a.loc.line b.loc.line = 0 then
          Stdlib.compare a.exp b.exp
        else Stdlib.compare a.loc.line b.loc.line
      else Stdlib.compare a.loc.file b.loc.file)
    queries

let sort_partition queries =
  List.sort
    (fun (a, _) (b, _) ->
      if Stdlib.compare a.file b.file = 0 then Stdlib.compare a.line b.line
      else Stdlib.compare a.file b.file)
    queries

let get_status queries =
  if List.exists (fun q -> q.status = BotAlarm) queries then BotAlarm
  else if List.exists (fun q -> q.status = UnProven) queries then UnProven
  else if List.for_all (fun q -> q.status = Proven) queries then Proven
  else raise (Failure "Report.ml: get_status")

let get_proved_query_point queries =
  let all = partition queries in
  let unproved = partition (get queries UnProven) in
  let all = BatMap.foldi (fun l _ -> BatSet.add l) all BatSet.empty in
  let unproved = BatMap.foldi (fun l _ -> BatSet.add l) unproved BatSet.empty in
  BatSet.diff all unproved

let string_of_query q =
  CilHelper.s_location q.loc ^ " " ^ AlarmExp.to_string q.exp ^ " @"
  ^ InterCfg.Node.to_string q.node
  ^ ":  "
  ^ (match q.allocsite with Some a -> Allocsite.to_string a | _ -> "")
  ^ "  " ^ q.desc ^ " "
  ^ status_to_string (get_status [ q ])

let filter_extern partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q ->
             match q.allocsite with
             | Some allocsite -> Allocsite.is_ext_allocsite allocsite
             | None -> false)
           ql))
    partition

let filter_global partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q -> InterCfg.Node.get_pid q.node = InterCfg.global_proc)
           ql))
    partition

let filter_lib partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q ->
             match q.exp with
             | AlarmExp.Strcpy (_, _, _)
             | AlarmExp.Strcat (_, _, _)
             | AlarmExp.Strncpy (_, _, _, _)
             | AlarmExp.Memcpy (_, _, _, _)
             | AlarmExp.Memmove (_, _, _, _) ->
                 true
             | _ -> false)
           ql))
    partition

let filter_rec global partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q -> Global.is_rec (InterCfg.Node.get_pid q.node) global)
           ql))
    partition

let filter_complex_exp partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q ->
             match q.exp with
             | AlarmExp.ArrayExp (_, BinOp (bop, _, _, _), _) ->
                 bop = BAnd || bop = BOr || bop = BXor
             | AlarmExp.ArrayExp (_, Lval (Var vi, _), _) -> vi.vglob
             | AlarmExp.DerefExp (Lval (Var vi, _), _) -> vi.vglob
             | _ -> false)
           ql))
    partition

let filter_allocsite partition =
  BatMap.filterv
    (fun ql ->
      not
        (List.exists
           (fun q ->
             match q.allocsite with
             | Some allocsite ->
                 BatSet.mem
                   (Allocsite.to_string allocsite)
                   !Options.filter_allocsite
             | None -> false)
           ql))
    partition

let filter_by_target_locs target_map =
  List.filter (fun alarm ->
      BatMap.exists
        (fun _ target_loc ->
          let file, line =
            match String.split_on_char ':' target_loc with
            | [ f; l ] -> (f, int_of_string l)
            | _ ->
                L.error
                  "Invalid slice option (must be '-target_alarm X=file:line')";
                exit 1
          in
          Filename.basename alarm.loc.file |> String.equal file
          && alarm.loc.line = line)
        target_map)

let alarm_filter global part =
  part
  |> opt !Options.filter_extern filter_extern
  |> opt !Options.filter_global filter_global
  |> opt !Options.filter_lib filter_lib
  |> opt !Options.filter_complex_exp filter_complex_exp
  |> opt !Options.filter_rec (filter_rec global)
  |> opt (not (BatSet.is_empty !Options.filter_allocsite)) filter_allocsite

let print_alarms fmt global queries =
  let all = partition queries in
  let unproven = partition (get queries UnProven) |> alarm_filter global in
  let proven = get_proved_query_point queries in
  let bot = partition (get queries BotAlarm) in
  let alarms_part = if !Options.show_all_query then all else unproven in
  F.fprintf fmt "= Alarms =\n";
  let alarms_part = BatMap.bindings alarms_part in
  let alarms_part = sort_partition alarms_part in
  List.iteri
    (fun k (part_unit, qs) ->
      F.fprintf fmt "%d. %s %s %s\n" (k + 1)
        (CilHelper.s_location part_unit)
        (string_of_set id
           (list2set (List.map (fun q -> InterCfg.Node.get_pid q.node) qs)))
        (status_to_string (get_status qs));
      List.iter
        (fun q ->
          F.fprintf fmt "  %s @%s:  %s %s" (AlarmExp.to_string q.exp)
            (InterCfg.Node.to_string q.node)
            q.desc
            (status_to_string (get_status [ q ]));
          match q.allocsite with
          | Some a -> F.fprintf fmt ", allocsite: %a\n" Allocsite.pp a
          | _ -> F.fprintf fmt "\n")
        qs)
    alarms_part;
  F.fprintf fmt "\n";
  F.fprintf fmt "#queries                 : %d\n" (List.length queries);
  F.fprintf fmt "#queries mod alarm point : %d\n" (BatMap.cardinal all);
  F.fprintf fmt "#proven                  : %d\n" (BatSet.cardinal proven);
  F.fprintf fmt "#unproven                : %d\n" (BatMap.cardinal unproven);
  F.fprintf fmt "#bot-involved            : %d\n" (BatMap.cardinal bot)

let print ?(fmt = None) global queries =
  if not !Options.noalarm then
    match fmt with
    | None ->
        let _ = prerr_newline () in
        let report_file = open_out (!Options.outdir ^ "/report.txt") in
        let file_fmt = F.formatter_of_out_channel report_file in
        let fmt = Logging.dual_formatter F.err_formatter file_fmt in
        print_alarms fmt global queries;
        close_out report_file
    | Some fmt -> print_alarms fmt global queries
  else ()
