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
(** Def-use graph *)

module type S = sig
  type t
  type node = BasicDom.Node.t

  module V = BasicDom.Node
  module Loc : AbsDom.SET
  module PowLoc : PowDom.CPO with type elt = Loc.t
  module Access : Access.S with type Loc.t = Loc.t and type PowLoc.t = PowLoc.t

  type path_checker

  val create : ?size:int -> ?access:Access.t -> unit -> t
  val copy : t -> t
  val clear : t -> unit
  val nb_node : t -> int
  val nb_edge : t -> int
  val nb_loc : t -> int
  val nodesof : t -> node BatSet.t
  val succ : node -> t -> node list
  val pred : node -> t -> node list
  val add_edge : node -> node -> t -> t
  val remove_edge : node -> node -> t -> t
  val remove_node : node -> t -> t
  val get_abslocs : node -> node -> t -> PowLoc.t
  val mem_node : node -> t -> bool
  val mem_duset : Loc.t -> PowLoc.t -> bool
  val add_absloc : node -> Loc.t -> node -> t -> t
  val add_abslocs : node -> PowLoc.t -> node -> t -> t
  val access : t -> Access.t
  val update_loopheads : node BatSet.t -> t -> t
  val update_backedges : (node, node list) BatMap.t -> t -> t
  val loopheads : t -> node BatSet.t
  val backedges : t -> (node, node list) BatMap.t
  val shortest_path : t -> node -> node -> node list
  val shortest_path_loc : t -> node -> node -> Loc.t -> node list
  val shortest_path_loc_str : t -> node -> node -> string -> node list
  val create_path_checker : t -> path_checker
  val check_path : path_checker -> node -> node -> bool
  val find_node_of_string : t -> string -> node option
  val transitive_closure : ?reflexive:bool -> t -> t

  (** {2 Iterator } *)

  val fold_node : (node -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges_e : (node -> node -> PowLoc.t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_vertex : (node -> unit) -> t -> unit
  val iter_node : (node -> unit) -> t -> unit
  val iter_edges : (node -> node -> unit) -> t -> unit
  val iter_edges_e : (node -> node -> PowLoc.t -> unit) -> t -> unit
  val fold_pred : (node -> 'a -> 'a) -> t -> node -> 'a -> 'a
  val fold_succ : (node -> 'a -> 'a) -> t -> node -> 'a -> 'a
  val iter_succ : (node -> unit) -> t -> node -> unit

  (** {2 Print } *)

  val to_dot : ?color:(node * string) list -> t -> string
  val to_json : t -> Yojson.Safe.t
end

module Make (Access : Access.S) :
  S
    with type Access.t = Access.t
     and type Loc.t = Access.Loc.t
     and type PowLoc.t = Access.PowLoc.t
