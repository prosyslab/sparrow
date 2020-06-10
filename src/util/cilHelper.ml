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
open Vocab
module F = Format

(* ******************* *
 * to_string functions *
 * ******************* *)

let tostring s = Escape.escape_string (Pretty.sprint ~width:0 s)

let rec s_exps es = string_of_list ~first:"(" ~last:")" ~sep:", " s_exp es

and s_exp = function
  | Const c -> s_const c
  | Lval l -> s_lv l
  | SizeOf t -> "SizeOf(" ^ s_type t ^ ")"
  | SizeOfE e -> "SizeOfE(" ^ s_exp e ^ ")"
  | SizeOfStr s -> "SizeOfStr(" ^ s ^ ")"
  | AlignOf t -> "AlignOf(" ^ s_type t ^ ")"
  | AlignOfE e -> "AlignOfE(" ^ s_exp e ^ ")"
  | UnOp (u, e, _) -> s_uop u ^ s_exp_paren e
  | BinOp (b, e1, e2, _) -> s_exp_paren e1 ^ s_bop b ^ s_exp_paren e2
  | Question (c, e1, e2, _) ->
      s_exp_paren c ^ " ? " ^ s_exp_paren e1 ^ " : " ^ s_exp_paren e2
  | CastE (t, e) -> "(" ^ s_type t ^ ")" ^ s_exp_paren e
  | AddrOf l -> "&" ^ s_lv l
  | AddrOfLabel _ -> invalid_arg "AddrOfLabel is not supported."
  | StartOf l -> "StartOf(" ^ s_lv l ^ ")"

and s_exp_paren e =
  match e with
  | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
  | _ -> s_exp e

and s_const c = tostring (d_const () c)

and s_type typ = tostring (d_type () typ)

and s_stmt s = tostring (d_stmt () s)

and s_lv (lh, offset) = s_lhost lh ^ s_offset offset

and s_lhost = function
  | Var vi -> (if vi.vglob then "@" else "") ^ vi.vname
  | Mem e -> "*" ^ s_exp_paren2 e

and s_exp_paren2 e =
  match e with
  | Lval (_, NoOffset) -> s_exp e
  | Lval _ | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
  | _ -> s_exp e

and s_offset = function
  | NoOffset -> ""
  | Field (fi, offset) -> "." ^ fi.fname ^ s_offset offset
  | Index (e, offset) -> "[" ^ s_exp e ^ "]" ^ s_offset offset

and s_uop u = tostring (d_unop () u)

and s_bop b = tostring (d_binop () b)

and s_instr i =
  match i with
  | Set (lv, exp, _) -> "Set(" ^ s_lv lv ^ "," ^ s_exp exp ^ ")"
  | Call (Some lv, fexp, params, _) ->
      s_lv lv ^ ":= Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Call (None, fexp, params, _) -> "Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Asm _ -> "Asm"

and s_instrs instrs = List.fold_left (fun s i -> s ^ s_instr i) "" instrs

let s_location loc =
  let file =
    try
      let idx = String.rindex loc.file '/' in
      let len = String.length loc.file in
      String.sub loc.file (idx + 1) (len - idx - 1)
    with _ -> loc.file
  in
  file ^ ":" ^ string_of_int loc.line

let eq_lval l1 l2 = s_lv l1 = s_lv l2

(* ************* *
 * Aux functions *
 * ************* *)

let rev_binop = function
  | Lt -> Gt
  | Gt -> Lt
  | Le -> Ge
  | Ge -> Le
  | Eq -> Eq
  | Ne -> Ne
  | _ -> invalid_arg "cilHelper.ml: rev_binop"

let not_binop = function
  | Lt -> Ge
  | Gt -> Le
  | Le -> Gt
  | Ge -> Lt
  | Eq -> Ne
  | Ne -> Eq
  | LAnd -> LOr
  | LOr -> LAnd
  | _ -> invalid_arg "cilHelper.ml: rev_binop"

let rec make_cond_simple cond =
  match cond with
  | BinOp (op, CastE (_, e1), e2, t) | BinOp (op, e1, CastE (_, e2), t) ->
      let newe = BinOp (op, e1, e2, t) in
      make_cond_simple newe
  | BinOp (op, Lval _, _, _)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
      Some cond
  | BinOp (op, e, Lval x, t)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
      Some (BinOp (rev_binop op, Lval x, e, t))
  | BinOp (op, BinOp (PlusA, Lval x, Lval y, t2), e, t) ->
      make_cond_simple (BinOp (op, Lval x, BinOp (MinusA, e, Lval y, t2), t))
  | BinOp (op, BinOp (MinusA, Lval x, Lval y, t2), e, t) ->
      make_cond_simple (BinOp (op, Lval x, BinOp (PlusA, e, Lval y, t2), t))
  | UnOp (LNot, BinOp (op, e1, e2, t2), _)
    when op = Lt || op = Gt || op = Le || op = Ge || op = Eq || op = Ne ->
      make_cond_simple (BinOp (not_binop op, e1, e2, t2))
  | UnOp (LNot, BinOp (op, e1, e2, t2), t1) when op = LAnd || op = LOr -> (
      let not_e1 = UnOp (LNot, e1, t1) in
      let not_e2 = UnOp (LNot, e2, t1) in
      match (make_cond_simple not_e1, make_cond_simple not_e2) with
      | Some e1', Some e2' -> Some (BinOp (not_binop op, e1', e2', t2))
      | _, _ -> None )
  | UnOp (LNot, UnOp (LNot, e, _), _) -> make_cond_simple e
  | UnOp (LNot, Lval _, _) -> Some cond
  | Lval _ -> Some cond
  | _ -> None

let rec remove_cast = function
  | Cil.CastE (_, e) -> remove_cast e
  | Cil.BinOp (b, e1, e2, t) -> Cil.BinOp (b, remove_cast e1, remove_cast e2, t)
  | Cil.UnOp (u, e, t) -> Cil.UnOp (u, remove_cast e, t)
  | e -> e

let rec remove_coeff = function
  | Cil.BinOp (Cil.Mult, Cil.SizeOfE _, e1, _)
  | Cil.BinOp (Cil.Mult, e1, Cil.SizeOfE _, _)
  | Cil.BinOp (Cil.Mult, Cil.SizeOf _, e1, _)
  | Cil.BinOp (Cil.Mult, e1, Cil.SizeOf _, _) ->
      remove_coeff e1
  | Cil.BinOp (b, e1, e2, t) ->
      Cil.BinOp (b, remove_coeff e1, remove_coeff e2, t)
  | Cil.UnOp (u, e, t) -> Cil.UnOp (u, remove_coeff e, t)
  | e -> e

let is_unsigned = function
  | Cil.TInt (i, _) ->
      i = Cil.IUChar || i = Cil.IUInt || i = Cil.IUShort || i = Cil.IULong
      || i = Cil.IULongLong
  | _ -> false

let is_constant_n n e =
  match Cil.isInteger e with Some i -> Int64.to_int i = n | None -> false

(* NOTE : Cil.bitsSizeOf often fails: just return top for the moment
 * Adhoc solution: To avoid this failure, translate original C sources
 * into "CIL" (using -il option) and analyze the CIL program. *)
let byteSizeOf typ =
  try Cil.bitsSizeOf typ / 8
  with e ->
    if !Options.verbose >= 2 then
      prerr_endline ("warn: Cil.bitsSizeOf (" ^ s_type typ ^ ")");
    raise e

let eq_typ t1 t2 =
  try Cil.typeSig t1 = Cil.typeSig t2
  with _ ->
    (* Cil.typeSig may raise an exception if it is a variable array type.
     * See https://github.com/KihongHeo/cil/blob/6dde2a7922489437f46e6bd994b639351b55bb00/src/cil.ml#L5998
     * Conservatively return false.
     *)
    false

let add_field_offset offset fi =
  Cil.addOffset (Cil.Field (fi, Cil.NoOffset)) offset

let add_index_offset offset exp =
  Cil.addOffset (Cil.Index (exp, Cil.NoOffset)) offset

module Lval = struct
  type t = Cil.lval

  let compare x y = compare (Hashtbl.hash x) (Hashtbl.hash y)

  let pp fmt x = F.fprintf fmt "%s" (s_lv x)
end

module Exp = struct
  type t = Cil.exp

  let compare x y = compare (Hashtbl.hash x) (Hashtbl.hash y)

  let pp fmt x = F.fprintf fmt "%s" (s_exp x)
end
