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
(** Abstract semantics of interval analysis *)

open ProsysCil

include
  AbsSem.S
    with type Dom.t = ItvDom.Mem.t
     and type Dom.A.t = BasicDom.Loc.t
     and type Dom.PowA.t = BasicDom.PowLoc.t

val var_of_varinfo : Cil.varinfo -> BasicDom.Proc.t -> BasicDom.Loc.t

val eval_lv :
  ?spec:Spec.t ->
  BasicDom.Proc.t ->
  Cil.lval ->
  ItvDom.Mem.t ->
  BasicDom.PowLoc.t

val eval :
  ?spec:Spec.t -> BasicDom.Proc.t -> Cil.exp -> ItvDom.Mem.t -> ItvDom.Val.t

val eval_array_alloc :
  ?spec:Spec.t ->
  BasicDom.Node.t ->
  Cil.exp ->
  bool ->
  bool ->
  Dom.t ->
  ItvDom.Val.t

val eval_string_alloc : BasicDom.Node.t -> string -> ItvDom.Val.t

val eval_callees :
  ?spec:Spec.t ->
  BasicDom.Proc.t ->
  Cil.exp ->
  Global.t ->
  ItvDom.Mem.t ->
  BasicDom.PowProc.t
