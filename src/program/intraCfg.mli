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

(** Intra-procedural CFG *)
module Node : sig
  include AbsDom.HASHABLE_SET

  val entry : t
  val exit : t
  val id : t -> int
end

module NodeSet : BatSet.S with type elt = Node.t

module Cmd : sig
  type t =
    | Cinstr of ProsysCil.Cil.instr list * ProsysCil.Cil.location
    | Cif of
        ProsysCil.Cil.exp
        * ProsysCil.Cil.block
        * ProsysCil.Cil.block
        * ProsysCil.Cil.location
    | CLoop of ProsysCil.Cil.location
    (* final graph has the following cmds only *)
    | Cset of ProsysCil.Cil.lval * ProsysCil.Cil.exp * ProsysCil.Cil.location
    | Cexternal of ProsysCil.Cil.lval * ProsysCil.Cil.location
    | Calloc of
        ProsysCil.Cil.lval * alloc * local * static * ProsysCil.Cil.location
    | Csalloc of ProsysCil.Cil.lval * string * ProsysCil.Cil.location
    | Cfalloc of
        ProsysCil.Cil.lval * ProsysCil.Cil.fundec * ProsysCil.Cil.location
    | Cassume of ProsysCil.Cil.exp * branch * ProsysCil.Cil.location
    | Ccall of
        ProsysCil.Cil.lval option
        * ProsysCil.Cil.exp
        * ProsysCil.Cil.exp list
        * ProsysCil.Cil.location
    | Creturn of ProsysCil.Cil.exp option * ProsysCil.Cil.location
    | Casm of
        ProsysCil.Cil.attributes
        * string list
        * (string option * string * ProsysCil.Cil.lval) list
        * (string option * string * ProsysCil.Cil.exp) list
        * string list
        * ProsysCil.Cil.location
    | Cskip of tag * ProsysCil.Cil.location

  and alloc = Array of ProsysCil.Cil.exp | Struct of ProsysCil.Cil.compinfo
  and local = bool
  and static = bool
  and branch = bool
  and tag = Unknown | ReturnNode | Branch | LoopHead

  val fromCilStmt : ProsysCil.Cil.stmtkind -> t
  val location_of : t -> ProsysCil.Cil.location
  val to_string : t -> string
end

type t
(** Abstract type of intra-procedural CFG *)

and node = Node.t
and cmd = Cmd.t

val init : ProsysCil.Cil.fundec -> ProsysCil.Cil.location -> t

val generate_global_proc :
  ProsysCil.Cil.global list -> ProsysCil.Cil.fundec -> t

val get_pid : t -> string
val get_formals : t -> ProsysCil.Cil.varinfo list
val get_scc_list : t -> node list list
val transitive_closure : ?reflexive:bool -> t -> t
val pp_node_like_interCfg : t -> Format.formatter -> node -> unit
val nodesof : t -> node list
val entryof : t -> node
val exitof : t -> node
val callof : node -> t -> node
val returnof : node -> t -> node
val is_entry : node -> bool
val is_exit : node -> bool
val is_callnode : node -> t -> bool
val is_returnnode : node -> t -> bool
val is_inside_loop : node -> t -> bool
val find_cmd : node -> t -> cmd
val unreachable_node : t -> NodeSet.t
val compute_scc : t -> t
val optimize : t -> t
val fold_node : (node -> 'a -> 'a) -> t -> 'a -> 'a
val fold_edges : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
val iter_node : (node -> unit) -> t -> unit
val iter_vertex : (node -> unit) -> t -> unit
val iter_edges : (node -> node -> unit) -> t -> unit

(** {2 Predecessors and Successors } *)

val pred : node -> t -> node list
val succ : node -> t -> node list

(** {2 Graph Manipulation } *)

val add_cmd : node -> cmd -> t -> t
val add_new_node : node -> cmd -> node -> t -> t
val add_node_with_cmd : node -> cmd -> t -> t
val add_edge : node -> node -> t -> t
val remove_node : node -> t -> t

(** {2 Dominators } *)

val compute_dom : t -> t

val dom_fronts : node -> t -> NodeSet.t
(** [dom_fronts n g] returns dominance frontiers of node [n] in graph [g] *)

val post_dom_fronts : node -> t -> NodeSet.t
val children_of_dom_tree : node -> t -> NodeSet.t
val parent_of_dom_tree : node -> t -> node option

(** {2 Print } *)

val print_dot : out_channel -> t -> unit
val to_json : t -> Yojson.Safe.t
val to_json_simple : t -> Yojson.Safe.t
