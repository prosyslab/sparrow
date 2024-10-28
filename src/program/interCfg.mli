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
(** Inter-procedural CFG *)

module Proc : AbsDom.HASHABLE_SET with type t = string

module ProcSet : BatSet.S with type elt = Proc.t

module Node : sig
  include AbsDom.HASHABLE_SET

  val get_pid : t -> Proc.t

  val get_cfgnode : t -> IntraCfg.Node.t

  val make : Proc.t -> IntraCfg.Node.t -> t
end

module NodeSet : BatSet.S with type elt = Node.t

type t
(** Abstract type of inter-procedural CFG *)

and pid = Proc.t

and node = Node.t

val global_proc : Proc.t

val start_node : node
(** Starting point of program *)

val init : ProsysCil.Cil.file -> t

val cfgof : t -> pid -> IntraCfg.t

val argsof : t -> pid -> ProsysCil.Cil.varinfo list

val cmdof : t -> Node.t -> IntraCfg.cmd

val pidsof : t -> pid list

val nodesof : t -> Node.t list

val entryof : t -> pid -> node

val exitof : t -> pid -> node

val callof : node -> t -> node

val returnof : node -> t -> node

val pred : node -> t -> node list

val succ : node -> t -> node list

val get_post_dom_fronts : node -> t -> NodeSet.t

val is_entry : node -> bool

val is_exit : node -> bool

val is_callnode : node -> t -> bool

val is_returnnode : node -> t -> bool

val is_inside_loop : node -> t -> bool

val callnodesof : t -> node list

val add_call_edge : Node.t -> Proc.t -> t -> t

val remove_call_edge : Node.t -> Proc.t -> t -> t

val get_callees : Node.t -> t -> ProcSet.t

val get_callers : t -> pid -> NodeSet.t

val is_def : pid -> t -> bool

val is_undef : pid -> t -> bool

val remove_function : pid -> t -> t

val remove_node : node -> t -> t

val unreachable_node : t -> NodeSet.t

val fold_cfgs : (Proc.t -> IntraCfg.t -> 'a -> 'a) -> t -> 'a -> 'a

val iter : (Proc.t -> IntraCfg.t -> unit) -> t -> unit

val nodes_of_pid : t -> pid -> Node.t list

val get_node_loc : t -> pid * IntraCfg.NodeSet.elt -> ProsysCil.Cil.location

val node_to_cmd : t -> Node.t -> string

val node_to_filename : t -> Node.t -> string

val node_to_lstr_abs : t -> Node.t -> string

val node_to_lstr : t -> Node.t -> string

val node_to_filtered_pid : t -> (string, string) BatMap.t -> Node.t -> string

val node_to_fstr : t -> (string, string) BatMap.t -> Node.t -> string

val find_target_func : t -> (string, string) BatMap.t -> NodeSet.t -> string

val is_func_name_invalid : t -> (string, string) BatMap.t -> Node.t -> bool

val nodes_of_line : t -> string -> NodeSet.t

(** {2 Print } *)

val to_json : t -> Yojson.Safe.t

val to_json_simple : t -> Yojson.Safe.t
