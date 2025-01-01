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
(** Call-graph *)

type t
(** Abstract type of call graph *)

val empty : unit -> t
val size : t -> int
val callees : InterCfg.pid -> t -> BasicDom.PowProc.t
val trans_callees : InterCfg.pid -> t -> BasicDom.PowProc.t
val trans_callers : InterCfg.pid -> t -> BasicDom.PowProc.t
val add_edge : InterCfg.pid -> InterCfg.pid -> t -> t
val remove_edge : InterCfg.pid -> InterCfg.pid -> t -> t
val remove_function : InterCfg.pid -> t -> t
val is_rec : t -> InterCfg.pid -> bool
val compute_transitive : t -> t
val find_back_edges : t -> (InterCfg.pid * InterCfg.pid) list

(** {2 Print } *)

val to_json : t -> Yojson.Safe.t
