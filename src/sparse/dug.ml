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

  val update_loopheads : node BatSet.t -> t -> t

  val loopheads : t -> node BatSet.t

  val shortest_path : t -> node -> node -> node list

  val shortest_path_loc : t -> node -> node -> Loc.t -> node list

  val shortest_path_loc_str : t -> node -> node -> string -> node list

  val find_node_of_string : t -> string -> node option

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

  val to_dot : ?color:(node * string) list -> t -> string

  val to_json : t -> Yojson.Safe.t
end

module Make (Access : Access.S) = struct
  type node = BasicDom.Node.t

  module PowLoc = Access.PowLoc
  module Loc = Access.Loc
  module Access = Access

  type locset = PowLoc.t

  module G = struct
    module I = Graph.Imperative.Digraph.ConcreteBidirectional (BasicDom.Node)

    module W = struct
      type edge = I.E.t

      type t = int

      let weight _ = 1

      let compare = compare

      let add = ( + )

      let zero = 0
    end

    module Dijkstra = Graph.Path.Dijkstra (I) (W)

    type t = { graph : I.t; label : (node * node, locset) Hashtbl.t }

    let create ~size () =
      { graph = I.create ~size (); label = Hashtbl.create (2 * size) }

    let copy g = { graph = I.copy g.graph; label = Hashtbl.copy g.label }

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
          f s d locset)
        g.graph a

    let iter_vertex f g = I.iter_vertex f g.graph

    let iter_edges f g = I.iter_edges f g.graph

    let fold_pred f g a = I.fold_pred f g.graph a

    let iter_edges_e f g =
      I.iter_edges
        (fun s d ->
          let locset = Hashtbl.find g.label (s, d) in
          f s d locset)
        g.graph

    let fold_succ f g a = I.fold_succ f g.graph a

    let iter_succ f g = I.iter_succ f g.graph

    let remove_vertex g n =
      I.remove_vertex g.graph n;
      g

    let add_edge_e g (s, locs, d) =
      Hashtbl.replace g.label (s, d) locs;
      I.add_edge g.graph s d;
      g

    let add_edge g s d = add_edge_e g (s, PowLoc.empty, d)

    let remove_edge g s d =
      I.remove_edge g.graph s d;
      Hashtbl.remove g.label (s, d);
      g

    let find_label g s d = Hashtbl.find g.label (s, d)

    let modify_edge_def def g s d f =
      try
        let old_label = find_label g s d in
        let new_label = f old_label in
        Hashtbl.replace g.label (s, d) new_label;
        g
      with _ -> add_edge_e g (s, def, d)

    let shortest_path_loc g src dst loc =
      let module W :
        Graph.Sig.WEIGHT with type t = int option and type edge = I.E.t = struct
        type edge = I.E.t

        type t = int option

        let weight edge =
          let src, dst = (I.E.src edge, I.E.dst edge) in
          try
            let locset = find_label g src dst in
            if PowLoc.mem loc locset then Some 1 else None
          with _ -> None

        let compare x y =
          match (x, y) with
          | Some x, Some y -> compare x y
          | Some _, None -> -1
          | None, Some _ -> 1
          | None, None -> 0

        let add x y =
          match (x, y) with
          | Some x, Some y -> Some (x + y)
          | None, _ | _, None -> None

        let zero = Some 0
      end in
      let module D = Graph.Path.Dijkstra (I) (W) in
      let path, w = D.shortest_path g.graph src dst in
      match w with None -> [] | Some _ -> path

    let shortest_path_loc_str g src dst loc =
      let module W :
        Graph.Sig.WEIGHT with type t = int option and type edge = I.E.t = struct
        type edge = I.E.t

        type t = int option

        let weight edge =
          try
            let src, dst = (I.E.src edge, I.E.dst edge) in
            let locset = find_label g src dst in
            if PowLoc.exists (fun x -> Loc.to_string x = loc) locset then Some 1
            else None
          with _ -> None

        let compare x y =
          match (x, y) with
          | Some x, Some y -> compare x y
          | Some _, None -> -1
          | None, Some _ -> 1
          | None, None -> 0

        let add x y =
          match (x, y) with
          | Some x, Some y -> Some (x + y)
          | None, _ | _, None -> None

        let zero = Some 0
      end in
      let module D = Graph.Path.Dijkstra (I) (W) in
      let path, w = D.shortest_path g.graph src dst in
      match w with None -> [] | Some _ -> path
  end

  type t = { graph : G.t; access : Access.t; loopheads : node BatSet.t }

  let create ?(size = 0) ?(access = Access.empty) () =
    { graph = G.create ~size (); access; loopheads = BatSet.empty }

  let copy dug =
    { graph = G.copy dug.graph; access = dug.access; loopheads = dug.loopheads }

  let nodesof dug = G.fold_vertex BatSet.add dug.graph BatSet.empty

  let access dug = dug.access

  let succ n dug = try G.succ dug.graph n with _ -> []

  let pred n dug = try G.pred dug.graph n with _ -> []

  let nb_node dug = G.nb_vertex dug.graph

  let nb_edge dug = G.nb_edge dug.graph

  let remove_node n dug = { dug with graph = G.remove_vertex dug.graph n }

  let add_edge src dst dug = { dug with graph = G.add_edge dug.graph src dst }

  let remove_edge src dst dug =
    try { dug with graph = G.remove_edge dug.graph src dst } with _ -> dug

  let get_abslocs src dst dug =
    try G.find_label dug.graph src dst with _ -> PowLoc.empty

  let mem_node n g = G.mem_vertex g.graph n

  let mem_duset x duset = PowLoc.mem x duset

  let add_edge_e dug e = { dug with graph = G.add_edge_e dug.graph e }

  let add_absloc src x dst dug =
    {
      dug with
      graph =
        G.modify_edge_def (PowLoc.singleton x) dug.graph src dst (PowLoc.add x);
    }

  let add_abslocs src xs dst dug =
    if PowLoc.is_empty xs then dug
    else
      {
        dug with
        graph = G.modify_edge_def xs dug.graph src dst (PowLoc.union xs);
      }

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

  let update_loopheads loopheads g = { g with loopheads }

  let loopheads g = g.loopheads

  let shortest_path g src dst =
    let el = G.Dijkstra.shortest_path g.graph.graph src dst |> fst in
    List.fold_left
      (fun l edge ->
        let src, dst = (G.I.E.src edge, G.I.E.dst edge) in
        match l with [] -> [ dst; src ] | _ -> dst :: l)
      [] el

  let shortest_path_loc g src dst loc =
    let el = G.shortest_path_loc g.graph src dst loc in
    List.fold_left
      (fun l edge ->
        let src, dst = (G.I.E.src edge, G.I.E.dst edge) in
        match l with [] -> [ dst; src ] | _ -> dst :: l)
      [] el

  let shortest_path_loc_str g src dst loc =
    let el = G.shortest_path_loc_str g.graph src dst loc in
    List.fold_left
      (fun l edge ->
        let src, dst = (G.I.E.src edge, G.I.E.dst edge) in
        match l with [] -> [ dst; src ] | _ -> dst :: l)
      [] el

  let find_node_of_string dug name =
    fold_node
      (fun node result ->
        if Option.is_some result then result
        else if BasicDom.Node.to_string node = name then Some node
        else None)
      dug None

  let to_dot ?(color = []) dug =
    "digraph dugraph {\n"
    ^ List.fold_left
        (fun str (node, color) ->
          str ^ "\""
          ^ BasicDom.Node.to_string node
          ^ "\"[style=filled, fillcolor=" ^ color ^ "]\n")
        "" color
    ^ fold_edges
        (fun src dst str ->
          let addrset = get_abslocs src dst dug in
          str ^ "\""
          ^ BasicDom.Node.to_string src
          ^ "\"" ^ " -> " ^ "\""
          ^ BasicDom.Node.to_string dst
          ^ "\"" ^ "[label=\"{"
          ^ PowLoc.fold (fun addr s -> Loc.to_string addr ^ "," ^ s) addrset ""
          ^ "}\"]" ^ ";\n")
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
               [
                 `String (BasicDom.Node.to_string src);
                 `String (BasicDom.Node.to_string dst);
                 `String
                   (PowLoc.fold
                      (fun addr s -> Loc.to_string addr ^ "," ^ s)
                      addrset "");
               ]
             :: edges)
           g [])
    in
    `Assoc [ ("nodes", nodes); ("edges", edges) ]
end
