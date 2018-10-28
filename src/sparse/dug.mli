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
module type S =
sig
  type t
  type node = BasicDom.Node.t
  module Loc : AbsDom.SET
  module PowLoc : PowDom.CPO with type elt = Loc.t
  module Access : Access.S with type Loc.t = Loc.t and type PowLoc.t = PowLoc.t

  val create            : ?size : int -> ?access : Access.t -> unit -> t
  val copy              : t -> t
  val nb_node           : t -> int
  val nb_edge           : t -> int
  val nb_loc            : t -> int
  val nodesof           : t -> node BatSet.t

  val succ              : node -> t -> node list
  val pred              : node -> t -> node list

  val add_edge          : node -> node -> t -> t
  val remove_node       : node -> t -> t
  val get_abslocs       : node -> node -> t -> PowLoc.t
  val mem_node          : node -> t -> bool
  val mem_duset         : Loc.t -> PowLoc.t -> bool
  val add_absloc        : node -> Loc.t -> node -> t -> t
  val add_abslocs       : node -> PowLoc.t -> node -> t -> t

  val access            : t -> Access.t

(** {2 Iterator } *)

  val fold_node         : (node -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges        : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges_e      : (node -> node -> PowLoc.t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_node         : (node -> unit) -> t -> unit
  val iter_edges        : (node -> node -> unit) -> t -> unit
  val iter_edges_e      : (node -> node -> PowLoc.t -> unit) -> t -> unit
  val fold_pred         : (node -> 'a ->'a) -> t -> node -> 'a -> 'a
  val fold_succ         : (node -> 'a ->'a) -> t -> node -> 'a -> 'a
  val iter_succ         : (node -> unit) -> t -> node -> unit

(** {2 Print } *)

  val to_dot            : t -> string
  val to_json           : t -> Yojson.Safe.json
end

module Make (Access : Access.S) : S
  with type Access.t = Access.t
   and type Loc.t = Access.Loc.t
   and type PowLoc.t = Access.PowLoc.t
