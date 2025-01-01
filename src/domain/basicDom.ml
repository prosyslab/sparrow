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
(** Abstract Domain *)

open Vocab
module Cil = ProsysCil.Cil
module Node = InterCfg.Node
module PowNode = PowDom.MakeCPO (Node)
module Proc = InterCfg.Proc
module PowProc = PowDom.MakeCPO (Proc)

module ExtAllocsite = struct
  type t = Input | Unknown of string [@@deriving compare]

  let input = Input
  let unknown s = Unknown s
  let is_cmd_arg x = match x with Unknown s -> s = "arg" | _ -> false

  let to_string = function
    | Input -> "__extern__"
    | Unknown s -> "__extern__" ^ s

  let pp fmt x = Format.fprintf fmt "%s" (to_string x)
end

module IntAllocsite = struct
  type t = Node.t * is_string
  and is_string = bool [@@deriving compare]

  let is_global_allocsite (node, _) =
    Proc.equal (Node.get_pid node) InterCfg.global_proc

  let to_string (node, _) = Node.to_string node
  let pp fmt x = Format.fprintf fmt "%s" (to_string x)
end

module Allocsite = struct
  type t =
    | Local of Node.t
    | Internal of IntAllocsite.t
    | External of ExtAllocsite.t
    | Super of string
  [@@deriving compare]

  let allocsite_of_local n = Local n
  let allocsite_of_node n = Internal (n, false)
  let allocsite_of_string n = Internal (n, true)
  let of_super s = Super s
  let is_node_allocsite = function Internal (_, false) -> true | _ -> false
  let is_string_allocsite = function Internal (_, true) -> true | _ -> false

  let is_global_allocsite = function
    | Internal a -> IntAllocsite.is_global_allocsite a
    | _ -> false

  let is_ext_allocsite = function External _ -> true | _ -> false

  let is_cmd_arg = function
    | External e -> ExtAllocsite.is_cmd_arg e
    | _ -> false

  let is_superloc = function Super _ -> true | _ -> false

  let allocsite_of_ext = function
    | None -> External ExtAllocsite.input
    | Some fid -> External (ExtAllocsite.unknown fid)

  let to_string = function
    | Local n -> Node.to_string n
    | Internal i -> IntAllocsite.to_string i
    | External e -> ExtAllocsite.to_string e
    | Super s -> s

  let pp fmt = function
    | Local n -> Format.fprintf fmt "%a" Node.pp n
    | Internal i -> Format.fprintf fmt "%a" IntAllocsite.pp i
    | External e -> Format.fprintf fmt "%a" ExtAllocsite.pp e
    | Super s -> Format.fprintf fmt "%s" s
end

module Loc = struct
  type t =
    | GVar of string * Cil.typ
    | LVar of Proc.t * string * Cil.typ
    | Allocsite of Allocsite.t
    | Field of t * field * Cil.typ

  and field = string

  let rec compare x y =
    match (x, y) with
    | GVar (g1, _), GVar (g2, _) -> String.compare g1 g2
    | LVar (p1, l1, _), LVar (p2, l2, _) ->
        let c = Proc.compare p1 p2 in
        if c = 0 then String.compare l1 l2 else c
    | Allocsite a1, Allocsite a2 -> Allocsite.compare a1 a2
    | Field (l1, f1, t1), Field (l2, f2, t2) ->
        let c = compare l1 l2 in
        if c = 0 then
          let c = String.compare f1 f2 in
          if c = 0 then Stdlib.compare (Cil.typeSig t1) (Cil.typeSig t2) else c
        else c
    | _, _ -> Stdlib.compare (tag_of_t x) (tag_of_t y)

  and tag_of_t = function
    | GVar _ -> 0
    | LVar _ -> 1
    | Allocsite _ -> 2
    | Field _ -> 3

  let equal = [%compare.equal: t]
  let hash = Hashtbl.hash

  let typ = function
    | GVar (_, t) | LVar (_, _, t) | Field (_, _, t) -> Some t
    | _ -> None

  let rec to_string = function
    | GVar (g, _) -> g
    | LVar (p, x, _) -> "(" ^ Proc.to_string p ^ "," ^ x ^ ")"
    | Allocsite a -> Allocsite.to_string a
    | Field (a, f, _) -> to_string a ^ "." ^ f

  let pp fmt x = Format.fprintf fmt "%s" (to_string x)
  let return_var_name = "__return__"
  let dummy = GVar ("__dummy__", Cil.voidType)
  let null = GVar ("NULL", Cil.voidPtrType)
  let is_null x = x = null
  let is_var = function GVar _ | LVar _ -> true | _ -> false
  let is_gvar = function GVar _ -> true | _ -> false
  let is_lvar = function LVar _ -> true | _ -> false
  let is_allocsite = function Allocsite _ -> true | _ -> false

  let is_super_allocsite = function
    | Allocsite a -> Allocsite.is_superloc a
    | _ -> false

  let is_string_allocsite = function
    | Allocsite a -> Allocsite.is_string_allocsite a
    | _ -> false

  let is_ext_allocsite = function
    | Allocsite a -> Allocsite.is_ext_allocsite a
    | _ -> false

  let is_field = function Field _ -> true | _ -> false

  let rec is_global = function
    | GVar _ -> true
    | LVar _ -> false
    | Allocsite _ -> false
    | Field (l, _, _) -> is_global l

  let rec is_heap = function
    | GVar _ -> false
    | LVar _ -> false
    | Allocsite (Local _) -> false
    | Allocsite _ -> true
    | Field (l, _, _) -> is_heap l

  let rec is_local_of pid = function
    | GVar _ -> false
    | LVar (p, _, _) -> p = pid
    (* Allocation converted from local variable declarations *)
    | Allocsite (Local n) -> Node.get_pid n = pid
    | Allocsite _ -> false
    | Field (l, _, _) -> is_local_of pid l

  let get_proc = function LVar (p, _, _) -> p | _ -> raise Not_found
  let of_gvar x typ = GVar (x, typ)
  let of_lvar p x typ = LVar (p, x, typ)
  let of_allocsite x = Allocsite x
  let return_var pid typ = LVar (pid, return_var_name, typ)
  let append_field x f typ = Field (x, f, typ)
end

module PowLoc = struct
  include PowDom.MakeCPO (Loc)

  let null = singleton Loc.null

  let prune op x e =
    match op with
    | Cil.Eq when Cil.isZero e -> meet x null
    | Cil.Ne when Cil.isZero e -> remove Loc.null x
    | _ -> x

  let append_field ls f =
    let add_appended l acc =
      if Loc.is_ext_allocsite l then add l acc
      else if Loc.is_null l || Loc.is_string_allocsite l then acc
      else add (Loc.append_field l f.Cil.fname f.Cil.ftype) acc
    in
    fold add_appended ls bot
end

module Dump = MapDom.MakeCPO (Proc) (PowLoc)
