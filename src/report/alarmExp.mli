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
(** Alarm Cil.expression *)

open ProsysCil

type t =
  | ArrayExp of Cil.lval * Cil.exp * Cil.location
  | DerefExp of Cil.exp * Cil.location
  | PlusIOExp of Cil.exp * Cil.location
  | MinusIOExp of Cil.exp * Cil.location
  | MultIOExp of Cil.exp * Cil.location
  | ShiftIOExp of Cil.exp * Cil.location
  | CastIOExp of Cil.exp * Cil.location
  | DivExp of Cil.exp * Cil.location
  | Strcpy of Cil.exp * Cil.exp * Cil.location
  | Strcat of Cil.exp * Cil.exp * Cil.location
  | Strncpy of Cil.exp * Cil.exp * Cil.exp * Cil.location
  | Memcpy of Cil.exp * Cil.exp * Cil.exp * Cil.location
  | Memmove of Cil.exp * Cil.exp * Cil.exp * Cil.location
  | BufferOverrunLib of string * Cil.exp list * Cil.location
  | AllocSize of string * Cil.exp * Cil.location
  | Printf of string * Cil.exp * Cil.location

val location_of : t -> Cil.location

val collect : Spec.analysis -> IntraCfg.cmd -> t list

val to_string : t -> string
