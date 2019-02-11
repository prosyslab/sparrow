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
(** Abstract semantics of octagon impact analysis *)

include
  AbsSem.S
  with type Dom.t = OctImpactDom.Mem.t
   and type Dom.A.t = OctDom.Pack.t
   and type Dom.PowA.t = OctDom.PackConf.t
