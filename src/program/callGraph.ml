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

  (* Since ocamlgraph does not maintain predecessor list, computing transitive
   * colsure takes too long. Rewrote the transitive closure computation logic in
   * https://github.com/backtracking/ocamlgraph/blob/1c028af0/src/oper.ml#L40 to
   * use a hash table for predecessors. *)

  let pred_hash = PredHash.create 10000

  let bootstrap g =
    PredHash.clear pred_hash;
    iter_edges
      (fun s d ->
        let old_pred =
          try PredHash.find pred_hash d with _ -> PowProc.empty
        in
        let new_pred = PowProc.add s old_pred in
        PredHash.replace pred_hash d new_pred)
      g

  let add_edge_htbl g s d =
    let old_pred = try PredHash.find pred_hash d with _ -> PowProc.empty in
    let new_pred = PowProc.add s old_pred in
    PredHash.replace pred_hash d new_pred;
    add_edge g s d

  let fold_pred_htbl f _ v a =
    let preds = try PredHash.find pred_hash v with _ -> PowProc.empty in
    PowProc.fold f preds a

  let add_transitive_closure_htbl g0 =
    let phi v g =
      fold_succ
        (fun sv g ->
          fold_pred_htbl
            (fun pv g ->
              add_edge_htbl g pv sv;
              g)
            g v g)
        g v g
    in
    fold_vertex phi g0 g0

  let transitive_closure g0 =
    bootstrap g0;
    add_transitive_closure_htbl (copy g0)

  let succ g pid = try succ g pid with _ -> []
end

type t = { graph : G.t; trans_calls : G.t }

let empty () = { graph = G.create (); trans_calls = G.create () }

let add_edge src dst g =
  G.add_edge g.graph src dst;
  g

let callees pid g = G.succ g.graph pid |> PowProc.of_list

let trans_callees pid g = G.succ g.trans_calls pid |> PowProc.of_list

let compute_trans_calls callgraph =
  let trans_calls = G.transitive_closure callgraph.graph in
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
