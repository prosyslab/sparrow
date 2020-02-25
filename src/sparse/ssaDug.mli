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

module type S = sig
  module Access : Access.S

  module DUGraph : Dug.S

  module PowLoc : PowDom.CPO

  type node = BasicDom.Node.t

  type loc

  val make :
    ?skip_nodes:BasicDom.Node.t BatSet.t ->
    Global.t * Access.t * PowLoc.t ->
    DUGraph.t

  val to_json_intra : DUGraph.t -> Access.t -> Yojson.Safe.t

  val to_json_inter : DUGraph.t -> Access.t -> Yojson.Safe.t
end

module Make (DUGraph : Dug.S) :
  S
    with type DUGraph.t = DUGraph.t
     and type Access.t = DUGraph.Access.t
     and type PowLoc.t = DUGraph.PowLoc.t
