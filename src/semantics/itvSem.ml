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
(** Semantics of interval analysis *)

open Vocab
open ProsysCil
open Cil
open AbsSem
open BasicDom
open ItvDom
open Global
module Dom = ItvDom.Mem
module Access = Dom.Access
module Spec = Spec.Make (Dom)
module Rel = RelSemantics

let provenance = ref Provenance.G.empty
let record_provenance = ref false

let start_provenance () =
  record_provenance := true;
  provenance := Provenance.G.empty

let finish_provenance () =
  record_provenance := false;
  !provenance

let provenance_list = ref []

let start_provenance_list () =
  record_provenance := true;
  provenance_list := [];
  provenance := Provenance.G.empty

let finish_provenance_list () =
  record_provenance := false;
  !provenance_list

(* ********************** *
 * Abstract memory access *
 * ********************** *)
let can_strong_update mode spec global lvs =
  if spec.Spec.unsound_update then true
  else
    match (mode, lvs) with
    | Weak, _ -> false
    | Strong, lvs' ->
        if PowLoc.cardinal lvs' = 1 then
          let lv = PowLoc.choose lvs' in
          Loc.is_gvar lv
          || (Loc.is_lvar lv && not (Global.is_rec (Loc.get_proc lv) global))
        else false

let lookup locs mem =
  if !Options.extract_datalog_fact then
    PowLoc.iter
      (fun l ->
        let rvset = Mem.find l mem |> Val.all_locs in
        PowLoc.iter
          (fun r -> provenance := Provenance.G.add_edge !provenance l r)
          rvset;
        (* for now, introduce dummy loc for provenance of non-pointer values *)
        provenance := Provenance.G.add_edge !provenance l Loc.dummy)
      locs;
  Mem.lookup locs mem

let update mode spec global locs v mem =
  let locs = PowLoc.remove Loc.null locs in
  if can_strong_update mode spec global locs then Mem.strong_update locs v mem
  else Mem.weak_update locs v mem

(* ********************************** *
 * Semantic functions for expressions *
 * ********************************** *)

let eval_const = function
  | Cil.CInt64 (i64, _, _) ->
      let itv = try Itv.of_int (Z.to_int i64) with _ -> Itv.top in
      Val.of_itv itv
  | Cil.CStr _ -> Val.of_itv Itv.top
  | Cil.CWStr _ -> Val.of_itv Itv.top
  | Cil.CChr c -> Val.of_itv (Itv.of_int (int_of_char c))
  (* Float numbers are modified to itvs.  If you want to make a
     precise and sound analysis for float numbers, you have to
     develop a domain for them. *)
  | Cil.CReal (f, _, _) ->
      Val.of_itv (Itv.of_ints (int_of_float (floor f)) (int_of_float (ceil f)))
  (* Enum is not evaluated correctly in our analysis. *)
  | Cil.CEnum _ -> Val.of_itv Itv.top

let eval_uop spec u v =
  if Val.eq v Val.bot then Val.bot
  else
    let itv = Val.itv_of_val v in
    let itv' =
      match u with
      | Cil.Neg -> Itv.minus (Itv.of_int 0) itv
      | Cil.LNot -> Itv.l_not itv
      | Cil.BNot ->
          if spec.Spec.unsound_bitwise then Itv.bot else Itv.unknown_unary itv
    in
    Val.of_itv itv'

let eval_bop spec b v1 v2 =
  match b with
  | Cil.PlusA -> Val.of_itv (Itv.plus (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.PlusPI | Cil.IndexPI ->
      let ablk = Val.array_of_val v1 in
      let offset = Val.itv_of_val v2 in
      let ablk = ArrayBlk.plus_offset ablk offset in
      Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk)
  | Cil.MinusA -> Val.of_itv (Itv.minus (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.MinusPI ->
      let ablk = Val.array_of_val v1 in
      let offset = Val.itv_of_val v2 in
      let ablk = ArrayBlk.minus_offset ablk offset in
      Val.join (Val.of_pow_loc (Val.pow_loc_of_val v1)) (Val.of_array ablk)
  | Cil.MinusPP ->
      let offset1 = Val.array_of_val v1 |> ArrayBlk.offsetof in
      let offset2 = Val.array_of_val v2 |> ArrayBlk.offsetof in
      Itv.minus offset1 offset2 |> Val.of_itv
  | Cil.Mult -> Val.of_itv (Itv.times (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Div -> Val.of_itv (Itv.divide (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Lt -> Val.of_itv (Itv.lt_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Gt -> Val.of_itv (Itv.gt_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Le -> Val.of_itv (Itv.le_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Ge -> Val.of_itv (Itv.ge_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Eq -> Val.of_itv (Itv.eq_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Ne -> Val.of_itv (Itv.ne_itv (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.LAnd -> Val.of_itv (Itv.l_and (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.LOr -> Val.of_itv (Itv.l_or (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Shiftlt ->
      if spec.Spec.unsound_bitwise then v1
      else Val.of_itv (Itv.l_shift (Val.itv_of_val v1) (Val.itv_of_val v2))
  | Cil.Shiftrt | Cil.Mod | Cil.BAnd | Cil.BXor | Cil.BOr ->
      if spec.Spec.unsound_bitwise then v1
      else
        Val.of_itv (Itv.unknown_binary (Val.itv_of_val v1) (Val.itv_of_val v2))

let rec resolve_offset spec pid v os mem =
  match os with
  | Cil.NoOffset ->
      PowLoc.join (Val.pow_loc_of_val v)
        (Val.array_of_val v |> ArrayBlk.pow_loc_of_array)
  | Cil.Field (f, os') ->
      let ploc, arr, str =
        (Val.pow_loc_of_val v, Val.array_of_val v, Val.struct_of_val v)
      in
      let v =
        lookup ploc mem |> Val.struct_of_val
        |> flip StructBlk.append_field f
        (* S s; p = &s; p->f *)
        |> PowLoc.join (ArrayBlk.append_field arr f)
        (* p = (struct S* )malloc(sizeof(struct S)); p->f *)
        |> PowLoc.join (StructBlk.append_field str f)
        (* S s; s.f *)
        |> Val.of_pow_loc
      in
      resolve_offset spec pid v os' mem
  | Cil.Index (e, os') ->
      let ploc = Val.pow_loc_of_val v in
      let arr = lookup ploc mem |> Val.array_of_val in
      let _ = eval ~spec pid e mem in
      (* NOTE: to sync with access function *)
      resolve_offset spec pid
        (ArrayBlk.pow_loc_of_array arr |> Val.of_pow_loc)
        os' mem

and eval_lv ?(spec = Spec.empty) pid lv mem =
  let v =
    match fst lv with
    | Cil.Var vi -> var_of_varinfo vi pid |> PowLoc.singleton |> Val.of_pow_loc
    | Cil.Mem e -> eval ~spec pid e mem
  in
  PowLoc.remove Loc.null (resolve_offset spec pid v (snd lv) mem)

and var_of_varinfo vi pid =
  if vi.Cil.vglob then Loc.of_gvar vi.Cil.vname vi.Cil.vtype
  else Loc.of_lvar pid vi.Cil.vname vi.Cil.vtype

and eval ?(spec = Spec.empty) pid e mem =
  match e with
  | Cil.Const c -> eval_const c
  | Cil.Lval l -> lookup (eval_lv ~spec pid l mem) mem
  | Cil.SizeOf t ->
      Val.of_itv (try CilHelper.byteSizeOf t |> Itv.of_int with _ -> Itv.pos)
  | Cil.SizeOfE e ->
      Val.of_itv
        (try CilHelper.byteSizeOf (Cil.typeOf e) |> Itv.of_int
         with _ -> Itv.pos)
  | Cil.SizeOfStr s -> Val.of_itv (Itv.of_int (String.length s + 1))
  | Cil.AlignOf t -> Val.of_itv (Itv.of_int (Cil.alignOf_int t))
  (* TODO: type information is required for precise semantics of AlignOfE. *)
  | Cil.AlignOfE _ -> Val.of_itv Itv.top
  | Cil.UnOp (u, e, _) -> eval_uop spec u (eval ~spec pid e mem)
  | Cil.BinOp (b, e1, e2, _) ->
      eval_bop spec b (eval ~spec pid e1 mem) (eval ~spec pid e2 mem)
  | Cil.Question (e1, e2, e3, _) ->
      let i1 = Val.itv_of_val (eval ~spec pid e1 mem) in
      if Itv.is_bot i1 then Val.bot
      else if Itv.eq (Itv.of_int 0) i1 then eval ~spec pid e3 mem
      else if not (Itv.le (Itv.of_int 0) i1) then eval ~spec pid e2 mem
      else Val.join (eval ~spec pid e2 mem) (eval ~spec pid e3 mem)
  | Cil.CastE (t, e) -> (
      let v = eval ~spec pid e mem in
      try Val.cast (Cil.typeOf e) t v with _ -> v)
  | Cil.AddrOf l -> eval_lv ~spec pid l mem |> Val.of_pow_loc
  | Cil.AddrOfLabel _ ->
      invalid_arg
        "itvSem.ml:eval AddrOfLabel mem. Analysis does not support label \
         values."
  | Cil.StartOf l -> lookup (eval_lv ~spec pid l mem) mem

let eval_list spec pid exps mem =
  List.map
    (fun e ->
      start_provenance ();
      let v = eval ~spec pid e mem in
      let prov = finish_provenance () in
      provenance_list := !provenance_list @ [ prov ];
      v)
    exps

let eval_array_alloc ?(spec = Spec.empty) node e is_local is_static mem =
  let pid = Node.pid node in
  let allocsite =
    if is_local then Allocsite.allocsite_of_local node
    else Allocsite.allocsite_of_node node
  in
  let o = Itv.of_int 0 in
  let sz = Val.itv_of_val (eval ~spec pid e mem) in
  (* NOTE: stride is always one when allocating memory. *)
  let st = Itv.of_int 1 in
  let np = Itv.nat in
  let pow_loc =
    if is_static || !Options.unsound_alloc then PowLoc.bot
    else PowLoc.singleton Loc.null
  in
  let array = ArrayBlk.make allocsite o sz st np in
  Val.join (Val.of_pow_loc pow_loc) (Val.of_array array)

let eval_struct_alloc lv comp = StructBlk.make lv comp |> Val.of_struct

let eval_string_alloc node s =
  let allocsite = Allocsite.allocsite_of_string node in
  let o = Itv.of_int 0 in
  let sz = Itv.of_int (String.length s + 1) in
  let st = Itv.of_int 1 in
  let np = Itv.of_int (String.length s) in
  let array = ArrayBlk.make allocsite o sz st np in
  Val.of_array array

let eval_string _ = Val.of_itv Itv.nat

(* ****************************** *
 * Semantic functions for pruning *
 * ****************************** *)

let rec prune_simple mode spec global pid cond mem =
  match cond with
  | BinOp (op, Lval x, e, _)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
      let x_lv = eval_lv ~spec pid x mem in
      if PowLoc.cardinal x_lv = 1 then
        let x_v = lookup x_lv mem in
        let e_v = eval ~spec pid e mem |> Val.itv_of_val in
        let x_itv = Val.itv_of_val x_v in
        let x_ploc = Val.pow_loc_of_val x_v in
        let x_itv = Itv.prune op x_itv e_v in
        let x_ploc = PowLoc.prune op x_ploc e in
        let x_pruned =
          Val.make
            ( x_itv,
              x_ploc,
              Val.array_of_val x_v,
              Val.struct_of_val x_v,
              Val.pow_proc_of_val x_v )
        in
        update mode spec global x_lv x_pruned mem
      else mem
  | BinOp (op, e1, e2, _) when op = LAnd || op = LOr ->
      let mem1 = prune_simple mode spec global pid e1 mem in
      let mem2 = prune_simple mode spec global pid e2 mem in
      if op = LAnd then Mem.meet mem1 mem2 else Mem.join mem1 mem2
  | UnOp (LNot, Lval x, _) ->
      let x_lv = eval_lv ~spec pid x mem in
      if PowLoc.cardinal x_lv = 1 then
        let x_v = lookup x_lv mem in
        let x_itv = Val.itv_of_val x_v in
        let e_v = Itv.zero in
        let x_itv = Itv.meet x_itv e_v in
        let x_pruned = Val.modify_itv x_itv x_v in
        update mode spec global x_lv x_pruned mem
      else mem
  | Lval x ->
      let x_lv = eval_lv ~spec pid x mem in
      if PowLoc.cardinal x_lv = 1 then
        let x_v = lookup x_lv mem in
        let x_itv = Val.itv_of_val x_v in
        let pos_x = Itv.meet x_itv Itv.pos in
        let neg_x = Itv.meet x_itv Itv.neg in
        let x_itv = Itv.join pos_x neg_x in
        let x_pruned = Val.modify_itv x_itv x_v in
        update mode spec global x_lv x_pruned mem
      else mem
  | _ -> mem

let prune mode spec global pid cond mem =
  match CilHelper.make_cond_simple cond with
  | None -> mem
  | Some cond_simple -> prune_simple mode spec global pid cond_simple mem

(* ******************************* *
 * Semantic functions for commands *
 * ******************************* *)
let sparrow_print spec pid exps mem loc =
  if !Options.verbose < 1 then ()
  else
    let vs = eval_list spec pid exps mem in
    let vs_str = string_of_list Val.to_string vs in
    let exps_str = string_of_list CilHelper.s_exp exps in
    Logging.info "sparrow_print (%s %@ %s) : %s\n" exps_str
      (CilHelper.s_location loc) vs_str

let sparrow_dump mem loc =
  if !Options.verbose < 1 then ()
  else
    Logging.info "sparrow_dump (%s) : \n%a\n" (CilHelper.s_location loc) Mem.pp
      mem

let return_struct_type f =
  match f.vtype with
  | Cil.TFun (Cil.TPtr (t, _), _, _, _) -> t
  | _ -> assert false

let model_alloc_one mode spec pid lvo f (mem, global) =
  match lvo with
  | None -> (mem, global)
  | Some lv ->
      let size =
        try Itv.of_int (return_struct_type f |> CilHelper.byteSizeOf)
        with _ -> Itv.top
      in
      let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
      let arr_val =
        ItvDom.Val.of_array
          (ArrayBlk.make allocsite Itv.zero Itv.one size Itv.nat)
      in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem =
        update mode spec global (eval_lv ~spec pid lv mem) arr_val mem
      in
      let mem = update mode spec global ext_loc Val.itv_top mem in
      (mem, global)

let model_realloc mode spec node (lvo, exps) (mem, global) =
  let pid = Node.pid node in
  match lvo with
  | Some lv -> (
      match exps with
      | _ :: size :: _ ->
          ( update mode spec global (eval_lv ~spec pid lv mem)
              (eval_array_alloc ~spec node size false false mem)
              mem,
            global )
      | _ -> raise (Failure "Error: arguments of realloc are not given"))
  | _ -> (mem, global)

let model_calloc mode spec node (lvo, exps) (mem, global) =
  let pid = Node.pid node in
  match lvo with
  | Some lv -> (
      match exps with
      | n :: size :: _ ->
          let new_size = Cil.BinOp (Cil.Mult, n, size, Cil.uintType) in
          ( update mode spec global (eval_lv ~spec pid lv mem)
              (eval_array_alloc ~spec node new_size false false mem)
              mem,
            global )
      | _ -> raise (Failure "Error: arguments of realloc are not given"))
  | _ -> (mem, global)

let model_scanf mode spec pid exps (mem, global) =
  match exps with
  | _ :: t ->
      List.fold_left
        (fun (mem, global) e ->
          match e with
          | Cil.AddrOf lv ->
              let mem =
                update mode spec global (eval_lv ~spec pid lv mem) Val.itv_top
                  mem
              in
              (mem, global)
          | _ -> (mem, global))
        (mem, global) t
  | _ -> (mem, global)

let model_strdup mode spec node (lvo, exps) (mem, global) =
  let pid = Node.pid node in
  match (lvo, exps) with
  | Some lv, str :: _ ->
      let allocsite = Allocsite.allocsite_of_node node in
      let str_val = eval ~spec pid str mem |> ItvDom.Val.array_of_val in
      let size = ArrayBlk.sizeof str_val in
      let null_pos = ArrayBlk.nullof str_val in
      let allocsites = ArrayBlk.pow_loc_of_array str_val in
      let offset = Itv.zero in
      let arr_val =
        ArrayBlk.make allocsite Itv.zero (Itv.minus size offset) Itv.one
          null_pos
      in
      let loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let v = Val.join (Val.of_array arr_val) (Val.of_pow_loc loc) in
      let mem = update mode spec global (eval_lv ~spec pid lv mem) v mem in
      let mem = update mode spec global loc (lookup allocsites mem) mem in
      (mem, global)
  | _ -> (mem, global)

let model_input mode spec node pid lvo (mem, global) =
  match lvo with
  | Some lv ->
      let allocsite = Allocsite.allocsite_of_node node in
      let ext_v = Val.external_value allocsite in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global (eval_lv ~spec pid lv mem) ext_v mem in
      let mem = update mode spec global ext_loc Val.itv_top mem in
      (mem, global)
  | _ -> (mem, global)

let model_assign mode spec pid (lvo, exps) (mem, global) =
  match (lvo, exps) with
  | Some lv, e :: _ ->
      let ploc = eval_lv ~spec pid lv mem in
      let v = eval ~spec pid e mem in
      (update mode spec global ploc v mem, global)
  | _, _ -> (mem, global)

let model_strlen mode spec pid (lvo, exps) (mem, global) =
  match (lvo, exps) with
  | Some lv, str :: _ ->
      let str_val = eval ~spec pid str mem in
      let null_pos = ArrayBlk.nullof (ItvDom.Val.array_of_val str_val) in
      let v = Val.of_itv (Itv.meet Itv.nat null_pos) in
      (update mode spec global (eval_lv ~spec pid lv mem) v mem, global)
  | _ -> (mem, global)

let rec model_fgets mode spec pid (lvo, exps) (mem, global) =
  match (lvo, exps) with
  | _, Lval buf :: size :: _ | _, StartOf buf :: size :: _ ->
      let size_itv = eval ~spec pid size mem |> ItvDom.Val.itv_of_val in
      let buf_lv = eval_lv ~spec pid buf mem in
      let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
      let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
      let buf_val =
        ArrayBlk.set_null_pos buf_arr (Itv.join Itv.zero size_itv)
        |> ItvDom.Val.of_array
      in
      mem
      |> update mode spec global buf_lv buf_val
      |> update mode spec global allocsites Val.itv_top
      |> fun mem -> (mem, global)
  | _, CastE (_, buf) :: size :: e ->
      model_fgets mode spec pid (lvo, buf :: size :: e) (mem, global)
  | _ -> (mem, global)

let rec model_sprintf mode spec pid (lvo, exps) (mem, global) =
  match exps with
  | [ Lval buf; str ] | [ StartOf buf; str ] ->
      (* format string *)
      let str_val = eval ~spec pid str mem |> ItvDom.Val.array_of_val in
      let arrays, null_pos =
        (ArrayBlk.pow_loc_of_array str_val, ArrayBlk.nullof str_val)
      in
      let buf_lv = eval_lv ~spec pid buf mem in
      let buf_arr = lookup buf_lv mem |> ItvDom.Val.array_of_val in
      let allocsites = ArrayBlk.pow_loc_of_array buf_arr in
      let buf_val =
        ArrayBlk.set_null_pos buf_arr null_pos |> ItvDom.Val.of_array
      in
      (mem
      |> update mode spec global buf_lv buf_val
      |> update mode spec global allocsites (lookup arrays mem)
      |>
      match lvo with
      | Some lv ->
          update mode spec global (eval_lv ~spec pid lv mem)
            (Val.of_itv null_pos)
      | _ -> id)
      |> fun mem -> (mem, global)
  | [ CastE (_, buf); str ] | [ buf; CastE (_, str) ] ->
      model_sprintf mode spec pid (lvo, [ buf; str ]) (mem, global)
  | _ -> (
      match lvo with
      | Some lv ->
          ( update mode spec global (eval_lv ~spec pid lv mem)
              (Val.of_itv Itv.nat) mem,
            global )
      | _ -> (mem, global))

(* argc, argv *)
let sparrow_arg mode spec pid exps (mem, global) =
  match exps with
  | Cil.Lval argc :: Cil.Lval argv :: _ ->
      let argv_a = Allocsite.allocsite_of_ext (Some "argv") in
      let argv_v = Val.of_array (ArrayBlk.input argv_a) in
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) in
      ( update mode spec global
          (eval_lv ~spec pid argc mem)
          (Val.of_itv Itv.pos) mem
        |> update mode spec global (eval_lv ~spec pid argv mem) argv_v
        |> update mode spec global
             (PowLoc.singleton (Loc.of_allocsite argv_a))
             arg_v
        |> update mode spec global
             (PowLoc.singleton (Loc.of_allocsite arg_a))
             (Val.of_itv Itv.top),
        global )
  | _ -> (mem, global)

(* optind, optarg *)
let sparrow_opt mode spec pid exps (mem, global) =
  match exps with
  | Cil.Lval optind :: Cil.Lval optarg :: _ ->
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let arg_v = Val.of_array (ArrayBlk.input arg_a) in
      ( update mode spec global
          (eval_lv ~spec pid optind mem)
          (Val.of_itv Itv.nat) mem
        |> update mode spec global (eval_lv ~spec pid optarg mem) arg_v
        |> update mode spec global
             (PowLoc.singleton (Loc.of_allocsite arg_a))
             (Val.of_itv Itv.top),
        global )
  | _ -> (mem, global)

let model_unknown mode spec pid lvo f (mem, global) =
  match lvo with
  | None -> (mem, global)
  | Some lv when Cil.isArithmeticType (Cil.unrollTypeDeep (Cil.typeOfLval lv))
    ->
      let ext_v =
        if CilHelper.is_unsigned (Cil.unrollTypeDeep (Cil.typeOfLval lv)) then
          Val.of_itv Itv.nat
        else Val.of_itv Itv.top
      in
      let mem = update mode spec global (eval_lv ~spec pid lv mem) ext_v mem in
      (mem, global)
  | Some lv ->
      let allocsite = Allocsite.allocsite_of_ext (Some f.vname) in
      let ext_v =
        ArrayBlk.extern allocsite
        |> ArrayBlk.cast_array (Cil.typeOfLval lv)
        |> Val.of_array
      in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem = update mode spec global (eval_lv ~spec pid lv mem) ext_v mem in
      let mem = update mode spec global ext_loc Val.itv_top mem in
      (mem, global)

let model_getpwent mode spec node pid lvo f (mem, global) =
  match (lvo, f.vtype) with
  | ( Some lv,
      Cil.TFun
        ((Cil.TPtr ((Cil.TComp (comp, _) as elem_t), _) as ptr_t), _, _, _) ) ->
      let struct_loc = eval_lv ~spec pid lv mem in
      let struct_v =
        eval_array_alloc ~spec node (Cil.SizeOf elem_t) false false mem
        |> Val.cast ptr_t (Cil.typeOfLval lv)
      in
      let field_loc =
        ArrayBlk.append_field
          (Val.array_of_val struct_v)
          (List.find (fun f -> f.fname = "pw_name") comp.cfields)
      in
      let allocsite = Allocsite.allocsite_of_ext (Some "getpwent.pw_name") in
      let ext_v = ArrayBlk.input allocsite |> Val.of_array in
      let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
      let mem =
        update mode spec global struct_loc struct_v mem
        |> update mode spec global field_loc ext_v
        |> update mode spec global ext_loc Val.itv_top
      in
      (mem, global)
  | _ -> (mem, global)

let rec model_strcpy mode spec node pid es (mem, global) =
  match es with
  | CastE (_, e) :: t -> model_strcpy mode spec node pid (e :: t) (mem, global)
  | [ dst; CastE (_, e) ] ->
      model_strcpy mode spec node pid [ dst; e ] (mem, global)
  | [ Lval dst; Lval src ]
  | [ StartOf dst; StartOf src ]
  | [ Lval dst; StartOf src ]
  | [ StartOf dst; Lval src ] ->
      let src_arr = Val.array_of_val (lookup (eval_lv ~spec pid src mem) mem) in
      let dst_arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem) mem) in
      let np = ArrayBlk.nullof src_arr in
      let newv = Val.of_array (ArrayBlk.set_null_pos dst_arr np) in
      let mem =
        mem |> update mode spec global (eval_lv ~spec pid dst mem) newv
      in
      (mem, global)
  | _ -> (mem, global)

let rec model_strcat mode spec node pid es (mem, global) =
  match es with
  | CastE (_, e) :: t -> model_strcat mode spec node pid (e :: t) (mem, global)
  | [ dst; CastE (_, e) ] ->
      model_strcat mode spec node pid [ dst; e ] (mem, global)
  | [ Lval dst; Lval src ]
  | [ StartOf dst; StartOf src ]
  | [ Lval dst; StartOf src ]
  | [ StartOf dst; Lval src ] ->
      let src_arr = Val.array_of_val (lookup (eval_lv ~spec pid src mem) mem) in
      let dst_arr = Val.array_of_val (lookup (eval_lv ~spec pid dst mem) mem) in
      let np = ArrayBlk.nullof src_arr in
      let newv = Val.of_array (ArrayBlk.plus_null_pos dst_arr np) in
      let mem =
        mem |> update mode spec global (eval_lv ~spec pid dst mem) newv
      in
      (mem, global)
  | _ -> (mem, global)

let rec model_strchr mode spec node pid (lvo, exps) (mem, global) =
  match (lvo, exps) with
  | Some _, CastE (_, e) :: t ->
      model_strchr mode spec node pid (lvo, e :: t) (mem, global)
  | Some lv, Lval str :: _ | Some lv, StartOf str :: _ ->
      let str_arr = Val.array_of_val (lookup (eval_lv ~spec pid str mem) mem) in
      let np = ArrayBlk.nullof str_arr in
      let newv = Val.of_array (ArrayBlk.plus_offset str_arr np) in
      let mem =
        mem |> update mode spec global (eval_lv ~spec pid lv mem) newv
      in
      (mem, global)
  | _, _ -> (mem, global)

let model_fread mode spec pid (lvo, exps) (mem, global) =
  match exps with
  | buf :: _ :: cnt :: _ -> (
      let size_itv = eval ~spec pid cnt mem in
      let arr = eval ~spec pid buf mem in
      let locs = Val.all_locs arr in
      let mem = update Weak spec global locs size_itv mem in
      match lvo with
      | Some lv ->
          let mem =
            update mode spec global (eval_lv ~spec pid lv mem) arr mem
          in
          (mem, global)
      | _ -> (mem, global))
  | _ -> (mem, global)

let model_memset mode spec pid (lvo, exps) (mem, global) =
  match exps with
  | buf :: v :: _ -> (
      let arr = eval ~spec pid buf mem in
      let init = eval ~spec pid v mem in
      let locs = Val.all_locs arr in
      let mem = update Weak spec global locs init mem in
      match lvo with
      | Some lv ->
          let mem =
            update mode spec global (eval_lv ~spec pid lv mem) arr mem
          in
          (mem, global)
      | _ -> (mem, global))
  | _ -> (mem, global)

let sparrow_array_init mode spec node pid exps (mem, global) =
  match (List.nth exps 0, List.nth exps 1) with
  | arr, Cil.Const (Cil.CInt64 (_, _, _)) ->
      let lv =
        eval ~spec pid arr mem |> Val.array_of_val |> ArrayBlk.pow_loc_of_array
      in
      let v =
        List.fold_left
          (fun v e -> Val.join (eval ~spec pid e mem) v)
          Val.bot (List.tl exps)
      in
      (update mode spec global lv v mem, global)
  | arr, Cil.Const (Cil.CStr _) ->
      let lv =
        eval ~spec pid arr mem |> Val.array_of_val |> ArrayBlk.pow_loc_of_array
      in
      let v =
        List.fold_left
          (fun v e ->
            match e with
            | Cil.Const (Cil.CStr s) -> Val.join (eval_string_alloc node s) v
            | _ -> v)
          Val.bot (List.tl exps)
      in
      (update mode spec global lv v mem, global)
  | _, _ -> (mem, global)

let mem_alloc_libs =
  [
    "__ctype_b_loc";
    "initscr";
    "newwin";
    "localtime";
    "getpwnam";
    "__errno_location";
    "opendir";
    "readdir";
    "fopen";
    "fdopen";
    "localtime";
  ]

let eval_src src_typ pid mem arg_e =
  match src_typ with
  | ApiSem.Value -> eval pid arg_e mem
  | ApiSem.Array ->
      let ploc = eval pid arg_e mem |> Val.all_locs in
      lookup ploc mem

let rec collect_src_vals arg_exps arg_typs pid mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ ApiSem.Src (ApiSem.Variable, src_typ) ] ->
      List.map (eval_src src_typ pid mem) arg_exps
  | _, ApiSem.Src (ApiSem.Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, ApiSem.Src (ApiSem.Fixed, src_typ) :: arg_typs_left
    ->
      let src_v = eval_src src_typ pid mem arg_e in
      src_v :: collect_src_vals arg_exps_left arg_typs_left pid mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_src_vals arg_exps_left arg_typs_left pid mem

let rec collect_dst_vals arg_exps arg_typs pid mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ ApiSem.Dst (ApiSem.Variable, _) ] ->
      List.map (fun e -> eval pid e mem) arg_exps
  | _, ApiSem.Dst (ApiSem.Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, ApiSem.Dst (ApiSem.Fixed, _) :: arg_typs_left ->
      let dst_v = eval pid arg_e mem in
      dst_v :: collect_dst_vals arg_exps_left arg_typs_left pid mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_dst_vals arg_exps_left arg_typs_left pid mem

let rec collect_buf_vals arg_exps arg_typs pid mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ ApiSem.Buf (ApiSem.Variable, _) ] ->
      List.map (fun e -> eval pid e mem) arg_exps
  | _, ApiSem.Buf (ApiSem.Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, ApiSem.Buf (ApiSem.Fixed, _) :: arg_typs_left ->
      let buf_v = eval pid arg_e mem in
      buf_v :: collect_buf_vals arg_exps_left arg_typs_left pid mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_buf_vals arg_exps_left arg_typs_left pid mem

let rec collect_size_vals arg_exps arg_typs node mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | arg_e :: arg_exps_left, ApiSem.Size :: arg_typs_left ->
      let size_v = eval node arg_e mem in
      size_v :: collect_size_vals arg_exps_left arg_typs_left node mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_size_vals arg_exps_left arg_typs_left node mem

let process_dst mode spec node pid src_vals global alloc mem dst_e =
  let src_v = List.fold_left Val.join Val.bot src_vals in
  let dst_loc = Val.all_locs (eval pid dst_e mem) in
  if alloc then
    let allocsite = Allocsite.allocsite_of_node node in
    let offset = Itv.of_int 0 in
    let sz = Itv.top in
    let st = Itv.of_int 1 in
    let np = Itv.nat in
    let array = ArrayBlk.make allocsite offset sz st np in
    let block_v = Val.of_array array in
    let loc = PowLoc.singleton @@ Loc.of_allocsite allocsite in
    let mem = update mode spec global loc src_v mem in
    update mode spec global dst_loc block_v mem
  else update mode spec global dst_loc src_v mem

let process_buf mode spec node global mem dst_e =
  let pid = Node.pid node in
  let buf_loc = Val.all_locs (eval pid dst_e mem) in
  update mode spec global buf_loc Val.itv_top mem

let process_struct_ptr mode spec node global mem ptr_e =
  let pid = Node.pid node in
  let struct_loc = Val.all_locs (eval pid ptr_e mem) in
  let allocsite = Allocsite.allocsite_of_node node in
  let ext_v = Val.external_value allocsite in
  let ext_loc = Val.all_locs ext_v in
  let mem = update mode spec global struct_loc ext_v mem in
  let mem = update mode spec global ext_loc ext_v mem in
  (mem, global)

let rec process_args mode spec node arg_exps arg_typs src_vals (mem, global) =
  let va_src_flag =
    List.exists
      (function ApiSem.Src (ApiSem.Variable, _) -> true | _ -> false)
      arg_typs
  in
  let pid = Node.pid node in
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> mem
  | _, [ ApiSem.Dst (ApiSem.Variable, alloc) ] ->
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      List.fold_left
        (process_dst mode spec node pid src_vals global alloc)
        mem arg_exps
  | _, ApiSem.Dst (ApiSem.Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, ApiSem.Dst (ApiSem.Fixed, alloc) :: arg_typs_left ->
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      let mem =
        process_dst mode spec node pid src_vals global alloc mem arg_e
      in
      process_args mode spec node arg_exps_left arg_typs_left src_vals
        (mem, global)
  | _, [ ApiSem.Buf (ApiSem.Variable, _) ] ->
      List.fold_left (process_buf mode spec node global) mem arg_exps
  | _, ApiSem.Buf (ApiSem.Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, ApiSem.Buf (ApiSem.Fixed, _) :: arg_typs_left ->
      let mem = process_buf mode spec node global mem arg_e in
      process_args mode spec node arg_exps_left arg_typs_left src_vals
        (mem, global)
  | arg_e :: arg_exps_left, ApiSem.StructPtr :: arg_typs_left ->
      let mem, global = process_struct_ptr mode spec node global mem arg_e in
      process_args mode spec node arg_exps_left arg_typs_left src_vals
        (mem, global)
  | _ :: arg_exps_left, ApiSem.Src _ :: arg_typs_left
  | _ :: arg_exps_left, ApiSem.Size :: arg_typs_left
  | _ :: arg_exps_left, ApiSem.Skip :: arg_typs_left ->
      process_args mode spec node arg_exps_left arg_typs_left src_vals
        (mem, global)

let gen_block mode spec node init_v (mem, global) =
  let allocsite = Allocsite.allocsite_of_node node in
  let offset = Itv.of_int 0 in
  let sz = Itv.top in
  let st = Itv.of_int 1 in
  let np = Itv.nat in
  let array = ArrayBlk.make allocsite offset sz st np in
  let block_v = Val.of_array array in
  let pow_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
  (update mode spec global pow_loc init_v mem, block_v)

let produce_ret mode spec node ret_typ va_src_flag src_vals dst_vals buf_vals
    size_vals (mem, global) =
  match ret_typ with
  | ApiSem.Const -> (mem, Val.itv_top)
  | ApiSem.TaintInput ->
      (* User input value (top itv & taintness) *)
      (mem, Val.itv_top)
  | ApiSem.SrcArg ->
      (* Src argument returned *)
      let _ = assert (List.length src_vals = 1) in
      (mem, List.hd src_vals)
  | ApiSem.SizeArg ->
      (* Integer between 0 ~ Size argument returned *)
      let _ = assert (List.length size_vals = 1) in
      (mem, List.hd size_vals)
  | ApiSem.TopWithSrcTaint ->
      (* Top itv & taintness of Src argument returned *)
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      (mem, Val.itv_top)
  | ApiSem.DstArg ->
      (* Dst argument returned *)
      let _ = assert (List.length dst_vals = 1) in
      (mem, List.hd dst_vals)
  | ApiSem.BufArg ->
      (* Buf argument returned *)
      let _ = assert (List.length buf_vals = 1) in
      (mem, List.hd buf_vals)
  | ApiSem.AllocConst ->
      (* New block, filled with given abstract val. *)
      gen_block mode spec node Val.itv_top (mem, global)
  | ApiSem.AllocDst ->
      (* New block, filled with Src argument *)
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      let src_v = List.fold_left Val.join Val.bot src_vals in
      gen_block mode spec node src_v (mem, global)
  | ApiSem.AllocBuf ->
      (* New block, filled with user input *)
      gen_block mode spec node Val.itv_top (mem, global)
  | ApiSem.AllocStruct ->
      (* Newly allocated struct *)
      let allocsite = Allocsite.allocsite_of_node node in
      let ext_v = Val.external_value allocsite in
      gen_block mode spec node ext_v (mem, global)

let handle_api mode spec node (lvo, exps) (mem, global) api_type =
  let pid = Node.pid node in
  let arg_typs = api_type.ApiSem.arg_typs in
  let ret_typ = api_type.ApiSem.ret_typ in
  let src_vals = collect_src_vals exps arg_typs pid mem in
  let dst_vals = collect_dst_vals exps arg_typs pid mem in
  let buf_vals = collect_buf_vals exps arg_typs pid mem in
  let size_vals = collect_size_vals exps arg_typs pid mem in
  let mem = process_args mode spec node exps arg_typs src_vals (mem, global) in
  match lvo with
  | Some lv ->
      let va_src_flag =
        List.exists
          (function ApiSem.Src (ApiSem.Variable, _) -> true | _ -> false)
          arg_typs
      in
      let mem, ret_v =
        produce_ret mode spec node ret_typ va_src_flag src_vals dst_vals
          buf_vals size_vals (mem, global)
      in
      update mode spec global (eval_lv ~spec pid lv mem) ret_v mem
  | None -> mem

let scaffolded_functions mode spec node pid (lvo, f, exps) (mem, global) =
  if !Options.scaffold then
    match f.vname with
    | "fgets" -> model_fgets mode spec pid (lvo, exps) (mem, global)
    | "sprintf" -> model_sprintf mode spec pid (lvo, exps) (mem, global)
    | "scanf" -> model_scanf mode spec pid exps (mem, global)
    | "getenv" -> model_input mode spec node pid lvo (mem, global)
    | "strdup" | "strndup" ->
        model_strdup mode spec node (lvo, exps) (mem, global)
    | "gettext" -> model_assign mode spec pid (lvo, exps) (mem, global)
    | "getpwent" -> model_getpwent mode spec node pid lvo f (mem, global)
    | "strcpy" -> model_strcpy mode spec node pid exps (mem, global)
    | "strcat" -> model_strcat mode spec node pid exps (mem, global)
    | "strchr" | "strrchr" ->
        model_strchr mode spec node pid (lvo, exps) (mem, global)
    | "memset" -> model_memset mode spec pid (lvo, exps) (mem, global)
    | "fread" -> model_fread mode spec pid (lvo, exps) (mem, global)
    | s when List.mem s mem_alloc_libs ->
        model_alloc_one mode spec pid lvo f (mem, global)
    | _ when ApiSem.ApiMap.mem f.vname ApiSem.api_map ->
        let api_type = ApiSem.ApiMap.find f.vname ApiSem.api_map in
        (handle_api mode spec node (lvo, exps) (mem, global) api_type, global)
    | _ -> model_unknown mode spec pid lvo f (mem, global)
  else model_unknown mode spec pid lvo f (mem, global)

let handle_undefined_functions mode spec node pid (lvo, f, exps) (mem, global)
    loc =
  match f.vname with
  | "sparrow_arg" -> sparrow_arg mode spec pid exps (mem, global)
  | "sparrow_opt" -> sparrow_opt mode spec pid exps (mem, global)
  | "sparrow_print" ->
      sparrow_print spec pid exps mem loc;
      (mem, global)
  | "sparrow_dump" ->
      sparrow_dump mem loc;
      (mem, global)
  | "sparrow_assume" -> (prune mode spec global pid (List.hd exps) mem, global)
  | "sparrow_array_init" ->
      sparrow_array_init mode spec node pid exps (mem, global)
  | "strlen" -> model_strlen mode spec pid (lvo, exps) (mem, global)
  | "realloc" -> model_realloc mode spec node (lvo, exps) (mem, global)
  | "calloc" -> model_calloc mode spec node (lvo, exps) (mem, global)
  | _ -> scaffolded_functions mode spec node pid (lvo, f, exps) (mem, global)

let bind_lvar :
    update_mode -> Spec.t -> Global.t -> Loc.t -> Val.t -> Mem.t -> Mem.t =
 fun mode spec global lvar v mem ->
  let l = PowLoc.singleton lvar in
  update mode spec global l v mem

let bind_arg_ids :
    update_mode ->
    Spec.t ->
    Global.t ->
    Val.t list ->
    Loc.t list ->
    Mem.t ->
    Mem.t =
 fun mode spec global vs arg_ids mem ->
  list_fold2_prefix (bind_lvar mode spec global) arg_ids vs mem

(* Binds a list of values to a set of argument lists.  If |args_set|
    > 1, the argument binding does weak update. *)
let bind_arg_lvars_set mode spec global arg_ids_set vs mem =
  let mode = if BatSet.cardinal arg_ids_set > 1 then AbsSem.Weak else mode in
  BatSet.fold (bind_arg_ids mode spec global vs) arg_ids_set mem

let eval_callees ?(spec = Spec.empty) pid fexp global mem =
  let fs = Val.pow_proc_of_val (eval ~spec pid fexp mem) in
  if !Options.cut_cyclic_call then
    PowProc.filter (fun f -> not (BatSet.mem (pid, f) global.cyclic_calls)) fs
  else fs

(* Default update option is weak update. *)
let run mode spec node (mem, global) =
  let pid = Node.pid node in
  match InterCfg.cmd_of global.icfg node with
  | IntraCfg.Cmd.Cset (l, e, _) ->
      start_provenance ();
      let ploc = eval_lv ~spec pid l mem in
      let v = eval ~spec pid e mem in
      let prov = finish_provenance () in
      let mem = update mode spec global ploc v mem in
      let relations =
        Provenance.set spec.analysis global.icfg node e ploc v prov
          global.relations
      in
      (mem, { global with relations })
  | IntraCfg.Cmd.Cexternal (l, _) -> (
      match Cil.typeOfLval l with
      | Cil.TInt (_, _) | Cil.TFloat (_, _) ->
          let ext_v = Val.of_itv Itv.top in
          let mem =
            update mode spec global (eval_lv ~spec pid l mem) ext_v mem
          in
          (mem, global)
      | _ ->
          let allocsite = Allocsite.allocsite_of_ext None in
          let ext_v = Val.external_value allocsite in
          let ext_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
          let mem =
            update mode spec global (eval_lv ~spec pid l mem) ext_v mem
          in
          let mem = update mode spec global ext_loc ext_v mem in
          (mem, global))
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Array e, is_local, is_static, _) ->
      let ploc = eval_lv ~spec pid l mem in
      let v = eval_array_alloc ~spec node e is_local is_static mem in
      let mem = update mode spec global ploc v mem in
      let relations =
        Provenance.alloc spec.analysis node l e ploc v global.relations
      in
      (mem, { global with relations })
  | IntraCfg.Cmd.Calloc (l, IntraCfg.Cmd.Struct s, _, _, _) ->
      let lv = eval_lv ~spec pid l mem in
      (update mode spec global lv (eval_struct_alloc lv s) mem, global)
  | IntraCfg.Cmd.Csalloc (l, s, _) ->
      if !Options.unsound_const_string then (mem, global)
      else
        let str_loc =
          Allocsite.allocsite_of_string node
          |> Loc.of_allocsite |> PowLoc.singleton
        in
        mem
        |> update mode spec global (eval_lv ~spec pid l mem)
             (eval_string_alloc node s)
        |> update mode spec global str_loc (eval_string s)
        |> fun mem -> (mem, global)
  | IntraCfg.Cmd.Cfalloc (l, fd, _) ->
      let clos = Val.of_pow_proc (PowProc.singleton fd.svar.vname) in
      (update mode spec global (eval_lv ~spec pid l mem) clos mem, global)
  | IntraCfg.Cmd.Cassume (e, _, _) ->
      let _ = eval ~spec pid e mem in
      (* for inspection *)
      (prune mode spec global pid e mem, global)
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, loc)
    when Global.is_undef f.vname global
         || ApiSem.ApiMap.mem f.vname ApiSem.api_map ->
      (* undefined library functions *)
      if
        BatSet.mem
          (CilHelper.s_location loc ^ ":" ^ f.vname)
          spec.Spec.unsound_lib
      then (mem, global)
      else
        let _ = eval_list spec pid arg_exps mem in
        (* for inspection *)
        handle_undefined_functions mode spec node pid (lvo, f, arg_exps)
          (mem, global) loc
  | IntraCfg.Cmd.Ccall (lvo, f, arg_exps, _) ->
      (* user functions *)
      let fs = eval_callees ~spec pid f global mem in
      let arg_lvars_of_proc f acc =
        let args = InterCfg.args_of global.icfg f in
        let lvars =
          List.map (fun x -> Loc.of_lvar f x.Cil.vname x.Cil.vtype) args
        in
        BatSet.add lvars acc
      in
      let arg_lvars_set = PowProc.fold arg_lvars_of_proc fs BatSet.empty in
      start_provenance_list ();
      let arg_vals = eval_list spec pid arg_exps mem in
      let prov_list = finish_provenance_list () in
      (* Even if 'fs' is empty, evaluate argument values to draw a sound DUG *)
      if PowProc.eq fs PowProc.bot then (mem, global)
      else
        let dump =
          match lvo with
          | None -> global.dump
          | Some lv ->
              let retvars_of_proc f acc =
                let ret = Loc.return_var f (Cil.typeOfLval lv) in
                PowLoc.add ret acc
              in
              let retvar_set = PowProc.fold retvars_of_proc fs PowLoc.empty in
              let _ = Mem.lookup retvar_set mem in
              PowProc.fold
                (fun f d -> Dump.weak_add f (eval_lv ~spec pid lv mem) d)
                fs global.dump
        in
        let mem =
          bind_arg_lvars_set mode spec global arg_lvars_set arg_vals mem
        in
        let relations =
          Provenance.call spec.analysis arg_lvars_set prov_list global.relations
        in
        (mem, { global with dump; relations })
  | IntraCfg.Cmd.Creturn (None, _) -> (mem, global)
  | IntraCfg.Cmd.Creturn (Some e, _) ->
      start_provenance ();
      let ploc = Loc.return_var pid (Cil.typeOf e) |> PowLoc.singleton in
      let v = eval ~spec pid e mem in
      let prov = finish_provenance () in
      let mem = update Weak spec global ploc v mem in
      let relations =
        Provenance.set spec.analysis global.icfg node e ploc v prov
          global.relations
      in
      (mem, { global with relations })
  | IntraCfg.Cmd.Cskip _ when InterCfg.is_return_node node global.icfg ->
      let callnode = InterCfg.call_of node global.icfg in
      (match InterCfg.cmd_of global.icfg callnode with
      | IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
          let callees = eval_callees ~spec pid f global mem in
          (* TODO: optimize this. memory access and du edges *)
          let retvar_set =
            PowProc.fold
              (fun f ->
                let ret = Loc.return_var f (Cil.typeOfLval lv) in
                PowLoc.add ret)
              callees PowLoc.empty
          in
          update Weak spec global (eval_lv ~spec pid lv mem)
            (lookup retvar_set mem) mem
      | _ -> mem)
      |> fun mem -> (mem, global)
  | IntraCfg.Cmd.Cskip _ -> (mem, global)
  | IntraCfg.Cmd.Casm _ -> (mem, global) (* Not supported *)
  | _ -> invalid_arg "itvSem.ml: run_cmd"

let initial _ = Mem.bot
