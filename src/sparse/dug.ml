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

open Vocab
open Global
open IntraCfg
open InterCfg
open BasicDom

module type S = sig
  type t

  type node = BasicDom.Node.t

  module Loc : AbsDom.SET

  module PowLoc : PowDom.CPO with type elt = Loc.t

  module Access : Access.S with type Loc.t = Loc.t and type PowLoc.t = PowLoc.t

  val create : ?size:int -> ?access:Access.t -> unit -> t

  val copy : t -> t

  val nb_node : t -> int

  val nb_edge : t -> int

  val nb_loc : t -> int

  val nodesof : t -> node BatSet.t

  val succ : node -> t -> node list

  val pred : node -> t -> node list

  val add_edge : node -> node -> t -> t

  val remove_node : node -> t -> t

  val get_abslocs : node -> node -> t -> PowLoc.t

  val mem_node : node -> t -> bool

  val mem_duset : Loc.t -> PowLoc.t -> bool

  val add_absloc : node -> Loc.t -> node -> t -> t

  val add_abslocs : node -> PowLoc.t -> node -> t -> t

  val access : t -> Access.t

  (** {2 Iterator } *)

  val fold_node : (node -> 'a -> 'a) -> t -> 'a -> 'a

  val fold_edges : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a

  val fold_edges_e : (node -> node -> PowLoc.t -> 'a -> 'a) -> t -> 'a -> 'a

  val iter_node : (node -> unit) -> t -> unit

  val iter_edges : (node -> node -> unit) -> t -> unit

  val iter_edges_e : (node -> node -> PowLoc.t -> unit) -> t -> unit

  val fold_pred : (node -> 'a -> 'a) -> t -> node -> 'a -> 'a

  val fold_succ : (node -> 'a -> 'a) -> t -> node -> 'a -> 'a

  val iter_succ : (node -> unit) -> t -> node -> unit

  (** {2 Print } *)

  val to_dot : t -> string

  val to_json : t -> Yojson.Safe.t
end

module Make (Access : Access.S) = struct
  type node = BasicDom.Node.t

  module PowLoc = Access.PowLoc
  module Loc = Access.Loc
  module Access = Access

  type loc = Loc.t

  type locset = PowLoc.t

  module G = struct
    module I = Graph.Imperative.Digraph.ConcreteBidirectional (BasicDom.Node)

    type t = {graph: I.t; label: (node * node, locset) Hashtbl.t}

    let create ~size () =
      {graph= I.create ~size (); label= Hashtbl.create (2 * size)}

    let copy g = {graph= I.copy g.graph; label= Hashtbl.copy g.label}

    let succ g n = I.succ g.graph n

    let pred g n = I.pred g.graph n

    let nb_vertex g = I.nb_vertex g.graph

    let nb_edge g = I.nb_edges g.graph

    let pred_e g n =
      I.pred g.graph n
      |> List.map (fun p -> (p, Hashtbl.find g.label (p, n), n))

    let mem_vertex g n = I.mem_vertex g.graph n

    let mem_edge g n1 n2 = I.mem_edge g.graph n1 n2

    let fold_vertex f g a = I.fold_vertex f g.graph a

    let fold_edges f g a = I.fold_edges f g.graph a

    let fold_edges_e f g a =
      I.fold_edges
        (fun s d ->
          let locset = Hashtbl.find g.label (s, d) in
          f s d locset )
        g.graph a

    let iter_vertex f g = I.iter_vertex f g.graph

    let iter_edges f g = I.iter_edges f g.graph

    let fold_pred f g a = I.fold_pred f g.graph a

    let iter_edges_e f g =
      I.iter_edges
        (fun s d ->
          let locset = Hashtbl.find g.label (s, d) in
          f s d locset )
        g.graph

    let fold_succ f g a = I.fold_succ f g.graph a

    let iter_succ f g = I.iter_succ f g.graph

    let remove_vertex g n = I.remove_vertex g.graph n ; g

    let add_edge_e g (s, locs, d) =
      Hashtbl.replace g.label (s, d) locs ;
      I.add_edge g.graph s d ;
      g

    let add_edge g s d = add_edge_e g (s, PowLoc.empty, d)

    let remove_edge g s d =
      I.remove_edge g.graph s d ;
      Hashtbl.remove g.label (s, d) ;
      g

    let find_label g s d = Hashtbl.find g.label (s, d)

    let modify_edge_def def g s d f =
      try
        let old_label = find_label g s d in
        let new_label = f old_label in
        Hashtbl.replace g.label (s, d) new_label ;
        g
      with _ -> add_edge_e g (s, def, d)
  end

  type t = {graph: G.t; access: Access.t}

  let create ?(size = 0) ?(access = Access.empty) () =
    {graph= G.create ~size (); access}

  let copy dug = {graph= G.copy dug.graph; access= dug.access}

  let nodesof dug = G.fold_vertex BatSet.add dug.graph BatSet.empty

  let access dug = dug.access

  let succ n dug = try G.succ dug.graph n with _ -> []

  let pred n dug = try G.pred dug.graph n with _ -> []

  let nb_node dug = G.nb_vertex dug.graph

  let nb_edge dug = G.nb_edge dug.graph

  let remove_node n dug = {dug with graph= G.remove_vertex dug.graph n}

  let add_edge src dst dug = {dug with graph= G.add_edge dug.graph src dst}

  let remove_edge src dst dug =
    try {dug with graph= G.remove_edge dug.graph src dst} with _ -> dug

  let get_abslocs src dst dug =
    try G.find_label dug.graph src dst with _ -> PowLoc.empty

  let mem_node n g = G.mem_vertex g.graph n

  let mem_duset x duset = PowLoc.mem x duset

  let add_edge_e dug e = {dug with graph= G.add_edge_e dug.graph e}

  let add_absloc src x dst dug =
    { dug with
      graph=
        G.modify_edge_def (PowLoc.singleton x) dug.graph src dst (PowLoc.add x)
    }

  let add_abslocs src xs dst dug =
    if PowLoc.is_empty xs then dug
    else
      {dug with graph= G.modify_edge_def xs dug.graph src dst (PowLoc.union xs)}

  let fold_node f g a = G.fold_vertex f g.graph a

  let fold_edges f g a = G.fold_edges f g.graph a

  let fold_edges_e f g a = G.fold_edges_e f g.graph a

  let iter_node f g = G.iter_vertex f g.graph

  let iter_vertex f g = G.iter_vertex f g.graph

  let iter_edges f g = G.iter_edges f g.graph

  let iter_edges_e f g = G.iter_edges_e f g.graph

  let fold_pred f g a = G.fold_pred f g.graph a

  let fold_succ f g a = G.fold_succ f g.graph a

  let iter_succ f g = G.iter_succ f g.graph

  let nb_loc dug =
    fold_edges
      (fun src dst size -> PowLoc.cardinal (get_abslocs src dst dug) + size)
      dug 0

  let succ_e n g = List.map (fun s -> (s, get_abslocs n s g)) (succ n g)

  let pred_e n g = List.map (fun p -> (p, get_abslocs p n g)) (pred n g)

  let to_dot dug =
    "digraph dugraph {\n"
    ^ fold_edges
        (fun src dst str ->
          let addrset = get_abslocs src dst dug in
          str ^ "\""
          ^ BasicDom.Node.to_string src
          ^ "\"" ^ " -> " ^ "\""
          ^ BasicDom.Node.to_string dst
          ^ "\"" ^ "[label=\"{"
          ^ PowLoc.fold (fun addr s -> Loc.to_string addr ^ "," ^ s) addrset ""
          ^ "}\"]" ^ ";\n" )
        dug ""
    ^ "}"

  let to_json g =
    let nodes =
      `List
        (fold_node
           (fun v nodes -> `String (BasicDom.Node.to_string v) :: nodes)
           g [])
    in
    let edges =
      `List
        (fold_edges
           (fun src dst edges ->
             let addrset = get_abslocs src dst g in
             `List
               [ `String (BasicDom.Node.to_string src)
               ; `String (BasicDom.Node.to_string dst)
               ; `String
                   (PowLoc.fold
                      (fun addr s -> Loc.to_string addr ^ "," ^ s)
                      addrset "") ]
             :: edges )
           g [])
    in
    `Assoc [("nodes", nodes); ("edges", edges)]
end
