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

open Vocab
open ProsysCil.Cil
open IntraCfg.Cmd
module Cil = ProsysCil.Cil

module Proc = struct
  include String

  let equal = ( = )
  let hash = Hashtbl.hash
  let to_string x = x
  let pp fmt x = Format.fprintf fmt "%s" x
end

module ProcSet = BatSet.Make (Proc)

type pid = Proc.t

module Node = struct
  type t = Proc.t * IntraCfg.Node.t [@@deriving compare, equal]

  let to_string (pid, node) = pid ^ "-" ^ IntraCfg.Node.to_string node
  let to_json x = `String (to_string x)
  let make pid node = (pid, node)
  let get_pid = fst
  let get_cfgnode = snd
  let hash = Hashtbl.hash
  let pp fmt (p, n) = Format.fprintf fmt "%a-%a" Proc.pp p IntraCfg.Node.pp n
end

module IntraNodeSet = IntraCfg.NodeSet
module NodeSet = BatSet.Make (Node)

type node = Node.t

type t = {
  cfgs : (pid, IntraCfg.t) BatMap.t;
  globals : Cil.global list;
  call_edges : (Node.t, ProcSet.t) BatMap.t;
}

let dummy = { cfgs = BatMap.empty; globals = []; call_edges = BatMap.empty }

let add_call_edge call_node pid g =
  let callees =
    (try BatMap.find call_node g.call_edges with _ -> ProcSet.empty)
    |> ProcSet.add pid
  in
  { g with call_edges = BatMap.add call_node callees g.call_edges }

let remove_call_edge call_node pid g =
  let callees =
    (try BatMap.find call_node g.call_edges with _ -> ProcSet.empty)
    |> ProcSet.remove pid
  in
  if ProcSet.is_empty callees then g
  else { g with call_edges = BatMap.add call_node callees g.call_edges }

let get_callees call_node g =
  try BatMap.find call_node g.call_edges with _ -> ProcSet.empty

let get_callers g pid =
  BatMap.foldi
    (fun call_node callees acc ->
      if ProcSet.mem pid callees then NodeSet.add call_node acc else acc)
    g.call_edges NodeSet.empty

let global_proc = "_G_"
let start_node = Node.make global_proc IntraCfg.Node.entry

let ignore_file regexps loc =
  List.exists (fun re -> Str.string_match re loc.file 0) regexps

let gen_cfgs file =
  let regexps =
    List.map
      (fun str -> Str.regexp (".*" ^ str ^ ".*"))
      !Options.unsound_skip_file
  in
  BatMap.add global_proc
    (IntraCfg.generate_global_proc file.Cil.globals
       (Cil.emptyFunction global_proc))
    (list_fold
       (fun g m ->
         match g with
         | Cil.GFun (f, loc) when not (ignore_file regexps loc) ->
             BatMap.add f.svar.vname (IntraCfg.init f loc) m
         | _ -> m)
       file.Cil.globals BatMap.empty)

let compute_dom_and_scc icfg =
  {
    icfg with
    cfgs =
      BatMap.map
        (fun cfg -> IntraCfg.compute_scc (IntraCfg.compute_dom cfg))
        icfg.cfgs;
  }

let remove_function pid icfg =
  let is_not_pid_node node _ = Node.get_pid node <> pid in
  {
    icfg with
    cfgs = BatMap.remove pid icfg.cfgs;
    call_edges = BatMap.filter is_not_pid_node icfg.call_edges;
  }

let cfgof g pid =
  try BatMap.find pid g.cfgs
  with Not_found ->
    prerr_endline ("InterCfg.cfgof " ^ pid);
    raise Not_found

let cmdof g (pid, node) = IntraCfg.find_cmd node (cfgof g pid)

let add_cmd g (pid, node) cmd =
  {
    g with
    cfgs = BatMap.add pid (IntraCfg.add_cmd node cmd (cfgof g pid)) g.cfgs;
  }

let nodes_of_pid g pid =
  List.map (Node.make pid) (IntraCfg.nodesof (cfgof g pid))

let fold_cfgs f g a = BatMap.foldi f g.cfgs a
let iter f g = BatMap.iter f g.cfgs
let map_cfgs f g = { g with cfgs = BatMap.map f g.cfgs }

let fold_node f icfg acc =
  fold_cfgs
    (fun pid cfg acc ->
      IntraCfg.fold_node (fun node acc -> f (Node.make pid node) acc) cfg acc)
    icfg acc

let nodesof g =
  BatMap.foldi
    (fun pid cfg ->
      List.append (List.map (fun n -> Node.make pid n) (IntraCfg.nodesof cfg)))
    g.cfgs []

let pidsof g = BatMap.foldi (fun pid _ acc -> pid :: acc) g.cfgs []
let is_def pid g = BatMap.mem pid g.cfgs
let is_undef pid g = not (BatMap.mem pid g.cfgs)
let is_entry = function _, node -> IntraCfg.is_entry node
let is_exit = function _, node -> IntraCfg.is_exit node
let is_callnode (pid, node) g = IntraCfg.is_callnode node (cfgof g pid)

let is_returnnode (pid, node) g =
  try IntraCfg.is_returnnode node (cfgof g pid) with _ -> false

let returnof (pid, node) g = (pid, IntraCfg.returnof node (cfgof g pid))
let is_inside_loop (pid, node) g = IntraCfg.is_inside_loop node (cfgof g pid)
let callof (pid, node) g = (pid, IntraCfg.callof node (cfgof g pid))
let argsof g pid = IntraCfg.get_formals (cfgof g pid)
let callnodesof g = List.filter (fun node -> is_callnode node g) (nodesof g)
let entryof _ pid = Node.make pid IntraCfg.Node.entry
let exitof _ pid = Node.make pid IntraCfg.Node.exit

let pred (pid, node) g =
  let intra_cfg = cfgof g pid in
  IntraCfg.pred node intra_cfg |> List.map (Node.make pid)

let succ (pid, node) g =
  let intra_cfg = cfgof g pid in
  IntraCfg.succ node intra_cfg |> List.map (Node.make pid)

let get_post_dom_fronts node g =
  let pid, node = node in
  let cfg = cfgof g pid in
  IntraCfg.NodeSet.fold
    (fun n acc -> NodeSet.add (Node.make pid n) acc)
    (IntraCfg.post_dom_fronts node cfg)
    NodeSet.empty

let unreachable_node_pid pid icfg =
  IntraNodeSet.fold
    (fun node -> NodeSet.add (pid, node))
    (IntraCfg.unreachable_node icfg)
    NodeSet.empty

let unreachable_node g =
  let add_unreachable_node pid icfg =
    NodeSet.union (unreachable_node_pid pid icfg)
  in
  fold_cfgs add_unreachable_node g NodeSet.empty

let remove_node (pid, intra_node) g =
  let intra_cfg = cfgof g pid in
  let intra_cfg = IntraCfg.remove_node intra_node intra_cfg in
  { g with cfgs = BatMap.add pid intra_cfg g.cfgs }

let print chan g = BatMap.iter (fun _ cfg -> IntraCfg.print_dot chan cfg) g.cfgs
let get_node_loc g node = cmdof g node |> IntraCfg.Cmd.location_of
let node_to_cmd g node = cmdof g node |> IntraCfg.Cmd.to_string
let node_to_filename g node = get_node_loc g node |> CilHelper.get_loc_filename
let node_to_lstr_abs g node = get_node_loc g node |> CilHelper.s_location_abs
let node_to_lstr g node = get_node_loc g node |> CilHelper.s_location

let node_to_filtered_pid g line_to_func node =
  BatMap.find (node_to_lstr g node) line_to_func
  |> Str.split (Str.regexp "___[0-9]+")
  |> List.hd

let node_to_fstr g line_to_func node =
  node_to_filename g node ^ ":" ^ node_to_filtered_pid g line_to_func node

let find_target_func g line_to_func targ_nodes =
  node_to_filtered_pid g line_to_func (NodeSet.min_elt targ_nodes)

let nodes_of_line g line =
  fold_node
    (fun node acc ->
      let loc =
        if String.contains line '/' then node_to_lstr_abs g node
        else node_to_lstr g node
      in
      if loc = line then NodeSet.add node acc else acc)
    g NodeSet.empty

let is_func_name_invalid g line_to_func node =
  (* XXX. Strangely, some line string is not recorded in global.line_to_func *)
  node_to_filename g node = ""
  || (not (BatMap.mem (node_to_lstr g node) line_to_func))
  || node_to_filtered_pid g line_to_func node = global_proc

let to_json g =
  `Assoc
    (BatMap.foldi
       (fun pid cfg json -> (pid, IntraCfg.to_json cfg) :: json)
       g.cfgs [])

let to_json_simple g =
  BatMap.fold
    (fun cfg json ->
      let cfg_json = IntraCfg.to_json_simple cfg in
      match (json, cfg_json) with
      | `Assoc [], _ -> cfg_json
      | `Assoc l1, `Assoc l2 ->
          let nodes1 = List.assoc "nodes" l1 in
          let nodes2 = List.assoc "nodes" l2 in
          let edges1 = List.assoc "edges" l1 in
          let edges2 = List.assoc "edges" l2 in
          let nodes =
            match (nodes1, nodes2) with
            | `Assoc l1, `Assoc l2 -> `Assoc (l1 @ l2)
            | _ -> failwith "Invalid format"
          in
          let edges =
            match (edges1, edges2) with
            | `List l1, `List l2 -> `List (l1 @ l2)
            | _ -> failwith "Invalid format"
          in
          `Assoc [ ("nodes", nodes); ("edges", edges) ]
      | _, _ -> failwith "Invalid format")
    g.cfgs (`Assoc [])

let print_json chan g = Yojson.Safe.pretty_to_channel chan (to_json g)

(*
  1. collect all strings in salloc(_,s) of program: S
  2. build a map from s \in S to lv: M
  3. replace each salloc(lv,s) by set(lv,M(s))
  4. insert salloc(lv,s) in _G_ for each (s,lv) \in M
*)

let collect_strs icfg =
  list_fold
    (fun n ->
      match cmdof icfg n with Csalloc (_, s, _) -> BatSet.add s | _ -> id)
    (nodesof icfg) BatSet.empty

let str_count = ref 0

let get_cstr_name () =
  str_count := !str_count + 1;
  "_zoo_cstr_" ^ i2s !str_count

let build_strmap strs =
  BatSet.fold
    (fun str map ->
      let name = get_cstr_name () in
      let lv = (Var (Cil.makeGlobalVar name Cil.charPtrType), NoOffset) in
      BatMap.add str lv map)
    strs BatMap.empty

let replace_salloc icfg strmap =
  let nodes = nodesof icfg in
  list_fold
    (fun n g ->
      match cmdof g n with
      | Csalloc (lhs, str, location) ->
          let rhs = Lval (BatMap.find str strmap) in
          let cmd = Cset (lhs, rhs, location) in
          add_cmd g n cmd
      | _ -> g)
    nodes icfg

let dummy_location = { line = 0; file = ""; byte = 0 }

let insert_salloc icfg strmap =
  let _G_ = cfgof icfg global_proc in
  let _G_with_sallocs =
    BatMap.foldi
      (fun str lhs g ->
        let entry = IntraCfg.entryof g in
        let _ = assert (List.length (IntraCfg.succ entry g) = 1) in
        let next = List.nth (IntraCfg.succ entry g) 0 in
        let cmd = Csalloc (lhs, str, dummy_location) in
        IntraCfg.add_new_node entry cmd next g)
      strmap _G_
  in
  { icfg with cfgs = BatMap.add global_proc _G_with_sallocs icfg.cfgs }

let opt_salloc icfg =
  let strs = collect_strs icfg in
  let strmap = build_strmap strs in
  let icfg = replace_salloc icfg strmap in
  let icfg = insert_salloc icfg strmap in
  icfg

let optimize_il icfg = icfg |> map_cfgs IntraCfg.optimize

(*  |> opt_salloc*)

let init file =
  {
    cfgs = gen_cfgs file;
    globals = file.Cil.globals;
    call_edges = BatMap.empty;
  }
  |> opt !Options.optil optimize_il
  |> compute_dom_and_scc
