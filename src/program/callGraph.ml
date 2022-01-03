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

open BasicDom
open InterCfg

module G = struct
  include Graph.Imperative.Digraph.Concrete (BasicDom.Proc)
  module PredHash = Hashtbl.Make (BasicDom.Proc)

  let pred_hash = PredHash.create 10000

  let add_edge g s d =
    let old_pred = try PredHash.find pred_hash d with _ -> PowProc.empty in
    let new_pred = PowProc.add s old_pred in
    PredHash.replace pred_hash d new_pred;
    add_edge g s d

  let fold_pred f _ v a =
    let preds = try PredHash.find pred_hash v with _ -> PowProc.empty in
    PowProc.fold f preds a

  let succ g pid = try succ g pid with _ -> []
end

module SCC = Graph.Components.Make (G)
module Oper = Graph.Oper.I (G)

type t = { graph : G.t; trans_calls : G.t }

let empty () = { graph = G.create (); trans_calls = G.create () }

let add_edge src dst g =
  G.add_edge g.graph src dst;
  g

let callees pid g = G.succ g.graph pid |> PowProc.of_list

let trans_callees pid g = G.succ g.trans_calls pid |> PowProc.of_list

let compute_trans_calls callgraph =
  let trans_calls = Oper.transitive_closure callgraph.graph in
  { callgraph with trans_calls }

let is_rec callgraph pid =
  if G.mem_vertex callgraph.trans_calls pid then
    let trans = G.succ callgraph.trans_calls pid in
    List.mem pid trans
  else
    (* conservative answer for exceptional cases (e.g., unreachable functions) *)
    true

let to_json g =
  let nodes =
    `List
      (G.fold_vertex
         (fun v nodes -> `String (Proc.to_string v) :: nodes)
         g.graph [])
  in
  let edges =
    `List
      (G.fold_edges
         (fun v1 v2 edges ->
           `List [ `String (Proc.to_string v1); `String (Proc.to_string v2) ]
           :: edges)
         g.graph [])
  in
  `Assoc [ ("nodes", nodes); ("edges", edges) ]

let remove_function pid callgraph =
  G.remove_vertex callgraph.graph pid;
  G.remove_vertex callgraph.trans_calls pid;
  callgraph
