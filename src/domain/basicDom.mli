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
(** Basic abstract domains *)

module Node = InterCfg.Node

module PowNode :
  PowDom.CPO with type t = PowDom.MakeCPO(Node).t and type elt = Node.t

module Proc = InterCfg.Proc

module PowProc :
  PowDom.CPO with type t = PowDom.MakeCPO(Proc).t and type elt = Proc.t

module IntAllocsite : sig
  type t
end

module ExtAllocsite : sig
  type t
end

module Allocsite : sig
  type t =
    | Local of Node.t
    | Internal of IntAllocsite.t
    | External of ExtAllocsite.t
    | Super of string

  include AbsDom.SET with type t := t

  val allocsite_of_local : Node.t -> t
  val allocsite_of_node : Node.t -> t
  val allocsite_of_string : Node.t -> t
  val of_super : string -> t
  val is_string_allocsite : t -> bool
  val is_global_allocsite : t -> bool
  val is_ext_allocsite : t -> bool
  val is_cmd_arg : t -> bool
  val allocsite_of_ext : string option -> t
end

module Loc : sig
  type t =
    | GVar of string * ProsysCil.Cil.typ
    | LVar of Proc.t * string * ProsysCil.Cil.typ
    | Allocsite of Allocsite.t
    | Field of t * field * ProsysCil.Cil.typ

  and field = string

  include AbsDom.HASHABLE_SET with type t := t

  val return_var_name : string
  val null : t
  val dummy : t
  val equal : t -> t -> bool
  val is_var : t -> bool
  val is_lvar : t -> bool
  val is_gvar : t -> bool
  val is_allocsite : t -> bool
  val is_super_allocsite : t -> bool
  val is_ext_allocsite : t -> bool
  val is_field : t -> bool
  val is_heap : t -> bool
  val of_gvar : string -> ProsysCil.Cil.typ -> t
  val of_lvar : Proc.t -> string -> ProsysCil.Cil.typ -> t
  val append_field : t -> field -> ProsysCil.Cil.typ -> t
  val of_allocsite : Allocsite.t -> t
  val return_var : Proc.t -> ProsysCil.Cil.typ -> t
  val is_global : t -> bool
  val is_local_of : Proc.t -> t -> bool
  val get_proc : t -> Proc.t
  val typ : t -> ProsysCil.Cil.typ option
end

module PowLoc : sig
  include PowDom.CPO

  val null : t
  val prune : ProsysCil.Cil.binop -> t -> ProsysCil.Cil.exp -> t
  val append_field : t -> ProsysCil.Cil.fieldinfo -> t
end
with type t = PowDom.MakeCPO(Loc).t
 and type elt = Loc.t

module Dump : MapDom.CPO with type A.t = Proc.t and type B.t = PowLoc.t
