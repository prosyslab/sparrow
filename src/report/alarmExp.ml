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
open IntraCfg
open Cmd
module F = Format

type t =
  | ArrayExp of lval * exp * location
  | DerefExp of exp * location
  | MulExp of exp * location
  | DivExp of exp * exp * location
  | Strcpy of exp * exp * location
  | Strcat of exp * exp * location
  | Strncpy of exp * exp * exp * location
  | Memcpy of exp * exp * exp * location
  | Memmove of exp * exp * exp * location
  | BufferOverrunLib of string * exp list * location
  | AllocSize of string * exp * location
  | Printf of string * exp * location

let to_string t =
  match t with
  | ArrayExp (lv, e, _) -> CilHelper.s_lv lv ^ "[" ^ CilHelper.s_exp e ^ "]"
  | DerefExp (e, _) -> "*(" ^ CilHelper.s_exp e ^ ")"
  | MulExp (e, _) -> CilHelper.s_exp e
  | DivExp (e1, e2, _) -> CilHelper.s_exp e1 ^ " / " ^ CilHelper.s_exp e2
  | Strcpy (e1, e2, _) ->
      "strcpy (" ^ CilHelper.s_exp e1 ^ ", " ^ CilHelper.s_exp e2 ^ ")"
  | Strncpy (e1, e2, e3, _) ->
      "strncpy (" ^ CilHelper.s_exp e1 ^ ", " ^ CilHelper.s_exp e2 ^ ", "
      ^ CilHelper.s_exp e3 ^ ")"
  | Memcpy (e1, e2, e3, _) ->
      "memcpy (" ^ CilHelper.s_exp e1 ^ ", " ^ CilHelper.s_exp e2 ^ ", "
      ^ CilHelper.s_exp e3 ^ ")"
  | Memmove (e1, e2, e3, _) ->
      "memmove (" ^ CilHelper.s_exp e1 ^ ", " ^ CilHelper.s_exp e2 ^ ", "
      ^ CilHelper.s_exp e3 ^ ")"
  | Strcat (e1, e2, _) ->
      "strcat (" ^ CilHelper.s_exp e1 ^ ", " ^ CilHelper.s_exp e2 ^ ")"
  | BufferOverrunLib (f, el, _) ->
      F.sprintf "%s(%s)" f (String.concat ", " (List.map CilHelper.s_exp el))
  | AllocSize (f, e, _) -> F.sprintf "%s(%s)" f (CilHelper.s_exp e)
  | Printf (f, e, _) -> F.sprintf "%s(%s)" f (CilHelper.s_exp e)

let location_of = function
  | ArrayExp (_, _, l)
  | DerefExp (_, l)
  | MulExp (_, l)
  | DivExp (_, _, l)
  | Strcpy (_, _, l)
  | Strncpy (_, _, _, l)
  | Memcpy (_, _, _, l)
  | Memmove (_, _, _, l)
  | Strcat (_, _, l)
  | BufferOverrunLib (_, _, l)
  | AllocSize (_, _, l)
  | Printf (_, _, l) ->
      l

(* NOTE: you may use Cil.addOffset or Cil.addOffsetLval instead of
   add_offset, append_field, and append_index. *)
let rec add_offset o orig_offset =
  match orig_offset with
  | NoOffset -> o
  | Field (f, o1) -> Field (f, add_offset o o1)
  | Index (e, o1) -> Index (e, add_offset o o1)

let append_field lv f = (fst lv, add_offset (Field (f, NoOffset)) (snd lv))

let append_index lv e = (fst lv, add_offset (Index (e, NoOffset)) (snd lv))

let rec c_offset lv offset loc =
  match offset with
  | NoOffset -> []
  | Field (f, o) -> c_offset (append_field lv f) o loc
  | Index (e, o) ->
      (ArrayExp (lv, e, loc) :: c_exp e loc)
      @ c_offset (append_index lv e) o loc

and c_lv lv loc =
  match lv with
  | Var v, offset -> c_offset (Var v, NoOffset) offset loc
  | Mem exp, offset ->
      (DerefExp (exp, loc) :: c_exp exp loc)
      @ c_offset (Mem exp, NoOffset) offset loc

and c_exp e loc =
  match e with
  | Lval lv -> c_lv lv loc
  | AlignOfE e -> c_exp e loc
  | UnOp (_, e, _) -> c_exp e loc
  | BinOp (bop, e1, e2, _) -> (
      match bop with
      | Mult when !Options.mul ->
          (MulExp (e, loc) :: c_exp e1 loc) @ c_exp e2 loc
      | Div | Mod -> (DivExp (e1, e2, loc) :: c_exp e1 loc) @ c_exp e2 loc
      | _ -> c_exp e1 loc @ c_exp e2 loc)
  | CastE (_, e) -> c_exp e loc
  | AddrOf lv -> c_lv lv loc
  | StartOf lv -> c_lv lv loc
  | _ -> []

and c_exps exps loc = List.fold_left (fun q e -> q @ c_exp e loc) [] exps

let query_lib =
  [
    "strcpy";
    "memcpy";
    "memmove";
    "strncpy";
    "strcat";
    "memchr";
    "strncmp";
    "sprintf";
  ]

let c_lib f es loc =
  match f.vname with
  | "strcpy" -> Strcpy (List.nth es 0, List.nth es 1, loc) :: c_exps es loc
  | "memcpy" ->
      Memcpy (List.nth es 0, List.nth es 1, List.nth es 2, loc) :: c_exps es loc
  | "memmove" ->
      Memmove (List.nth es 0, List.nth es 1, List.nth es 2, loc)
      :: c_exps es loc
  | "strncpy" ->
      Strncpy (List.nth es 0, List.nth es 1, List.nth es 2, loc)
      :: c_exps es loc
  | "strcat" -> Strcat (List.nth es 0, List.nth es 1, loc) :: c_exps es loc
  | ("memchr" | "strncmp" | "sprintf") when List.length es > 2 ->
      BufferOverrunLib
        (f.vname, [ List.nth es 0; List.nth es 1; List.nth es 2 ], loc)
      :: c_exps es loc
  | _ -> []

let c_lib_taint f es loc =
  match f.vname with
  | "mmap" | "realloc" | "g_realloc" | "g_realloc_n" ->
      [ AllocSize (f.vname, List.nth es 1, loc) ]
  | "calloc" | "g_malloc" | "g_malloc_n" | "g_malloc0" | "g_try_malloc"
  | "g_try_malloc_n" | "__builtin_alloca" ->
      [ AllocSize (f.vname, List.nth es 0, loc) ]
  | "printf" -> [ Printf (f.vname, List.nth es 0, loc) ]
  | "fprintf" | "sprintf" | "vfprintf" | "vsprintf" | "vasprintf" | "__asprintf"
  | "asprintf" | "vdprintf" | "dprintf" | "easprintf" | "evasprintf" ->
      Printf (f.vname, List.nth es 1, loc)
      ::
      (if !Options.patron && List.length es > 2 then
       [
         BufferOverrunLib
           (f.vname, [ List.nth es 0; List.nth es 1; List.nth es 2 ], loc);
       ]
      else [])
  | "snprintf" | "vsnprintf" -> [ Printf (f.vname, List.nth es 2, loc) ]
  | _ -> []

let collect_interval = function
  | Cmd.Cset (lv, e, loc) -> c_lv lv loc @ c_exp e loc
  | Cmd.Cexternal (lv, loc) -> c_lv lv loc
  | Cmd.Calloc (lv, Array e, _, loc) -> c_lv lv loc @ c_exp e loc
  | Cmd.Csalloc (lv, _, loc) -> c_lv lv loc
  | Cmd.Cassume (e, _, loc) -> c_exp e loc
  | Cmd.Creturn (Some e, loc) -> c_exp e loc
  | Cmd.Ccall (_, Lval (Var f, NoOffset), es, loc)
    when List.mem f.vname query_lib ->
      c_lib f es loc
  | Cmd.Ccall (None, e, es, loc) -> c_exp e loc @ c_exps es loc
  | Cmd.Ccall (Some lv, e, es, loc) -> c_lv lv loc @ c_exp e loc @ c_exps es loc
  | _ -> []

let collect_taint = function
  | Cmd.Calloc (_, Array e, _, loc) ->
      AllocSize ("malloc", e, loc) :: c_exp e loc
  | Cmd.Ccall (_, Lval (Var f, NoOffset), es, loc) ->
      c_lib_taint f es loc @ c_exps es loc
  | Cmd.Ccall (_, _, es, loc) -> c_exps es loc
  | Cmd.Cset (_, e, loc) -> c_exp e loc
  | Cmd.Cassume (e, _, loc) -> c_exp e loc
  | Cmd.Creturn (Some e, loc) -> c_exp e loc
  | _ -> []

let collect analysis cmd =
  match analysis with
  | Spec.Interval | Octagon -> collect_interval cmd
  | Taint -> collect_taint cmd
  | _ -> []
