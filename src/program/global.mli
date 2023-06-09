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
(** Global information *)

type t = {
  file : Cil.file;
  icfg : InterCfg.t;
  callgraph : CallGraph.t;
  dump : BasicDom.Dump.t;
  mem : ItvDom.Mem.t;
  table : ItvDom.Table.t;
  relations : RelSemantics.Set.t;
  line_to_func : (string, string) BatMap.t;
  cyclic_calls : (InterCfg.pid * InterCfg.pid) BatSet.t;
}

val init : Cil.file -> t

val is_rec : InterCfg.pid -> t -> bool

val is_undef : InterCfg.pid -> t -> bool

val handle_cyclic_call : t -> t

val build_line_to_func_map : t -> t

val remove_functions : BasicDom.PowProc.t -> t -> t

val remove_unreachable_functions : t -> t
