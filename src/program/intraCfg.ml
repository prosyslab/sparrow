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
(** CFG for a Function. *)

open Vocab
open Cil

module Node = struct
  type t = ENTRY | EXIT | Node of int [@@deriving compare]

  let equal n1 n2 =
    match (n1, n2) with
    | ENTRY, ENTRY -> true
    | EXIT, EXIT -> true
    | Node i1, Node i2 -> i1 = i2
    | _, _ -> false

  let hash = Hashtbl.hash
  let entry = ENTRY
  let exit = EXIT
  let nid = ref 0

  let fromCilStmt s =
    if !nid < s.sid then nid := s.sid;
    Node s.sid

  let make () =
    nid := !nid + 1;
    Node !nid

  let id = function ENTRY | EXIT -> -1 | Node id -> id

  let to_string = function
    | ENTRY -> "ENTRY"
    | EXIT -> "EXIT"
    | Node i -> string_of_int i

  let pp fmt n = Format.fprintf fmt "%s" (to_string n)
end

module NodeSet = BatSet.Make (Node)

module Cmd = struct
  type t =
    | Cinstr of instr list * location
    | Cif of exp * block * block * location
    | CLoop of location
    (* final graph has the following cmds only *)
    | Cset of lval * exp * location
    | Cexternal of lval * location
    | Calloc of lval * alloc * local * static * location
    | Csalloc of lval * string * location
    | Cfalloc of lval * fundec * location
    | Cassume of exp * branch * location
    | Ccall of lval option * exp * exp list * location
    | Creturn of exp option * location
    | Casm of
        attributes
        * string list
        * (string option * string * lval) list
        * (string option * string * exp) list
        * string list
        * location
    | Cskip of tag * location

  and alloc = Array of exp | Struct of compinfo
  and local = bool
  and static = bool
  and branch = bool
  and tag = Unknown | ReturnNode | Branch | LoopHead

  let fromCilStmt = function
    | Instr instrs as s -> Cinstr (instrs, Cil.get_stmtLoc s)
    | If (exp, b1, b2, loc) -> Cif (exp, b1, b2, loc)
    | Loop (_, loc, _, _) -> CLoop loc
    | Return (expo, loc) -> Creturn (expo, loc)
    | s -> Cskip (Unknown, Cil.get_stmtLoc s)

  let string_of_tag = function
    | Unknown -> ""
    | ReturnNode -> "ReturnNode"
    | Branch -> "Branch"
    | LoopHead -> "LoopHead"

  open CilHelper

  let to_string = function
    | Cinstr (instrs, _) -> s_instrs instrs
    | Cset (lv, e, _) -> "set(" ^ s_lv lv ^ "," ^ s_exp e ^ ")"
    | Cexternal (lv, _) -> "extern(" ^ s_lv lv ^ ")"
    | Calloc (lv, Array e, _, _, _) ->
        "alloc(" ^ s_lv lv ^ ",[" ^ s_exp e ^ "])"
    | Calloc (lv, Struct compinfo, _, _, _) ->
        "alloc(" ^ s_lv lv ^ ",{" ^ compinfo.cname ^ "})"
    | Csalloc (lv, s, _) -> "salloc(" ^ s_lv lv ^ ", \"" ^ s ^ "\")"
    | Cfalloc (lv, f, _) -> "falloc(" ^ s_lv lv ^ ", " ^ f.svar.vname ^ ")"
    | Ccall (Some lv, fexp, params, _) ->
        s_lv lv ^ ":= call(" ^ s_exp fexp ^ ", " ^ s_exps params ^ ")"
    | Ccall (None, fexp, params, _) ->
        "call(" ^ s_exp fexp ^ s_exps params ^ ")"
    | Creturn (Some e, _) -> "return " ^ s_exp e
    | Creturn (None, _) -> "return"
    | Cif (_, _, _, _) -> "if"
    | Cassume (e, _, _) -> "assume(" ^ s_exp e ^ ")"
    | CLoop _ -> "loop"
    | Casm _ -> "asm"
    | Cskip _ -> "skip"

  let to_json = function
    | Cinstr (_, _) -> `List []
    | Cset (lv, e, _) ->
        `List [ `String "set"; `String (s_lv lv); `String (s_exp e) ]
    | Cexternal (lv, _) -> `List [ `String "extern"; `String (s_lv lv) ]
    | Calloc (lv, Array e, _, _, _) ->
        `List [ `String "alloc"; `String (s_lv lv); `String (s_exp e) ]
    | Calloc (lv, Struct compinfo, _, _, _) ->
        `List [ `String "alloc"; `String (s_lv lv); `String compinfo.cname ]
    | Csalloc (lv, s, _) ->
        `List [ `String "salloc"; `String (s_lv lv); `String ("\"" ^ s ^ "\"") ]
    | Cfalloc (lv, f, _) ->
        `List [ `String "falloc"; `String (s_lv lv); `String f.svar.vname ]
    | Ccall (Some lv, fexp, params, _) ->
        `List
          [
            `String "call";
            `String (s_lv lv);
            `String (s_exp fexp);
            `String (s_exps params);
          ]
    | Ccall (None, fexp, params, _) ->
        `List
          [
            `String "call"; `Null; `String (s_exp fexp); `String (s_exps params);
          ]
    | Creturn (Some e, _) -> `List [ `String "return"; `String (s_exp e) ]
    | Creturn (None, _) -> `List [ `String "return"; `Null ]
    | Cassume (e, b, _) ->
        `List [ `String "assume"; `Bool b; `String (s_exp e) ]
    | Cskip (tag, _) -> `List [ `String "skip"; `String (string_of_tag tag) ]
    | _ -> `List [ `String "skip"; `String "" ]

  let location_of = function
    | Cinstr (_, l)
    | Cif (_, _, _, l)
    | CLoop l
    | Cset (_, _, l)
    | Cexternal (_, l)
    | Calloc (_, _, _, _, l)
    | Csalloc (_, _, l)
    | Cfalloc (_, _, l)
    | Ccall (_, _, _, l)
    | Creturn (_, l) ->
        l
    | Cassume (_, _, l) -> l
    | Cskip (_, l) -> l
    | _ -> Cil.locUnknown
end

type node = Node.t
type cmd = Cmd.t

module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)
module Oper = Graph.Oper.P (G)
module Merge = Graph.Merge.P (G)
module Topo = Graph.Topological.Make (G)
module Scc = Graph.Components.Make (G)

module GDom = struct
  module V = Node

  type t = G.t

  let empty () = G.empty
  let fromG g = g
  let pred = G.pred
  let succ = G.succ
  let fold_vertex = G.fold_vertex
  let iter_vertex = G.iter_vertex
  let iter_succ = G.iter_succ
  let nb_vertex = G.nb_vertex
  let add_edge g _ _ = g
  let create : ?size:int -> unit -> t = fun ?size:_ () -> empty ()
end

module Dom = Graph.Dominator.Make_graph (GDom)

type t = {
  fd : Cil.fundec;
  graph : G.t;
  cmd_map : (node, cmd) BatMap.t;
  dom_fronts : dom_fronts;
  dom_tree : dom_tree;
  post_dom_fronts : dom_fronts;
  scc_list : node list list;
}

and dom_fronts = (Node.t, NodeSet.t) BatMap.t
and dom_tree = G.t

let empty fd =
  {
    fd;
    graph = G.empty;
    cmd_map = BatMap.empty;
    dom_fronts = BatMap.empty;
    post_dom_fronts = BatMap.empty;
    dom_tree = G.empty;
    scc_list = [];
  }

let pid g = g.fd.svar.vname
let get_formals g = g.fd.sformals
let get_formals_lval g = List.map Cil.var g.fd.sformals
let get_scc_list g = g.scc_list

let transitive_closure ?(reflexive = false) g =
  { g with graph = Oper.transitive_closure ~reflexive g.graph }

let pp_node_like_interCfg g fmt node =
  Format.fprintf fmt "%s-%s" (pid g) (Node.to_string node)

let children_of_dom_tree node g =
  NodeSet.remove node (NodeSet.of_list (G.succ g.dom_tree node))

let parent_of_dom_tree node g =
  match G.pred g.dom_tree node with
  | [] -> None
  | [ p ] -> Some p
  | _ -> raise (Failure "IntraCfg.parent_of_dom_tree: fatal")

let dom_fronts node g = BatMap.find node g.dom_fronts
let post_dom_fronts node g = BatMap.find node g.post_dom_fronts
let nodes_of g = G.fold_vertex (fun x l -> x :: l) g.graph []
let add_edge n1 n2 g = { g with graph = G.add_edge g.graph n1 n2 }
let add_node n g = { g with graph = G.add_vertex g.graph n }

let find_cmd n g =
  try BatMap.find n g.cmd_map
  with _ ->
    if n = Node.ENTRY || n = Node.EXIT then
      Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)
    else Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)
(* else raise (Failure ("Can't find cmd of " ^ Node.to_string n)) *)

let add_cmd n c g = { g with cmd_map = BatMap.add n c g.cmd_map }
let add_node_with_cmd n c g = g |> add_node n |> add_cmd n c
let remove_edge n1 n2 g = { g with graph = G.remove_edge g.graph n1 n2 }

let remove_node n g =
  {
    g with
    graph = G.remove_vertex g.graph n;
    cmd_map = BatMap.remove n g.cmd_map;
    dom_fronts = BatMap.remove n g.dom_fronts;
    dom_tree = G.remove_vertex g.dom_tree n;
  }

(* should be used only after all Cil nodes are made *)
let add_new_node n cmd s g =
  let new_node = Node.make () in
  (add_cmd new_node cmd >>> remove_edge n s >>> add_edge n new_node
 >>> add_edge new_node s)
    g

(* TODO: optimize G.pred *)
let pred n g = G.pred g.graph n
let succ n g = G.succ g.graph n
let fold_node f g a = G.fold_vertex f g.graph a
let fold_edges f g a = G.fold_edges f g.graph a
let iter_node f g = G.iter_vertex f g.graph
let iter_vertex f g = G.iter_vertex f g.graph
let iter_edges f g = G.iter_edges f g.graph
let is_entry_node = function Node.ENTRY -> true | _ -> false
let is_exit_node = function Node.EXIT -> true | _ -> false

let is_call_node n g =
  match find_cmd n g with Cmd.Ccall _ -> true | _ -> false

let is_return_node n g =
  let preds = pred n g in
  List.length preds = 1 && is_call_node (List.hd preds) g

let entry_of _ = Node.ENTRY
let exit_of _ = Node.EXIT

let return_of n g =
  if is_call_node n g then (
    assert (List.length (succ n g) = 1);
    List.hd (succ n g))
  else failwith "IntraCfg.returnof: given node is not a call-node"

let is_inside_loop n g =
  List.exists (fun scc -> List.length scc > 1 && List.mem n scc) g.scc_list

let call_of r g =
  let preds = pred r g in
  assert (List.length preds = 1);
  List.hd preds

let generate_assumes g =
  try
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cif (e, tb, fb, loc) ->
            let succs = succ n g in
            (* successors of if-node *)
            let _ = assert (List.length succs = 1 || List.length succs = 2) in
            if List.length succs = 2 then
              (* normal case *)
              let s1, s2 = (List.nth succs 0, List.nth succs 1) in
              let tbn, fbn =
                (* true-branch node, false-branch node *)
                match (tb.bstmts, fb.bstmts) with
                | [], [] -> (s1, s2)
                | t :: _, _ -> if t.sid = Node.id s1 then (s1, s2) else (s2, s1)
                | _, t :: _ -> if t.sid = Node.id s2 then (s1, s2) else (s2, s1)
              in
              let tassert = Cmd.Cassume (e, true, loc) in
              let not_e = UnOp (LNot, e, Cil.typeOf e) in
              let fassert = Cmd.Cassume (not_e, false, loc) in
              (add_new_node n fassert fbn >>> add_new_node n tassert tbn) g
            else
              (* XXX : when if-statement has only one successor.
                        seems to happen inside dead code *)
              let tbn = List.nth succs 0 in
              let tassert = Cmd.Cassume (e, true, loc) in
              add_new_node n tassert tbn g
        | _ -> g)
      g g
  with _ -> assert false

(* If and Loop are unnecessary in cfg *)
let remove_if_loop g =
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cif (_, _, _, l) -> add_cmd n (Cmd.Cskip (Cmd.Branch, l)) g
      | Cmd.CLoop l -> add_cmd n (Cmd.Cskip (Cmd.LoopHead, l)) g
      | _ -> g)
    g g

(* remove all nodes s.t. n1 -> empty_node -> n2 *)
let remove_empty_nodes g =
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cskip _
        when List.length (succ n g) = 1 && List.length (pred n g) = 1 ->
          let p = List.nth (pred n g) 0 in
          let s = List.nth (succ n g) 0 in
          g |> remove_node n |> add_edge p s
      | _ -> g)
    g g

(* split instructions into set/call/asm *)
let flatten_instructions g =
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cinstr (instrs, _) when instrs <> [] ->
          let cmds =
            List.map
              (fun i ->
                match i with
                | Set (lv, e, loc) -> Cmd.Cset (lv, e, loc)
                | Call (lvo, f, args, loc) -> Cmd.Ccall (lvo, f, args, loc)
                | Asm (a, b, c, d, e, f) -> Cmd.Casm (a, b, c, d, e, f))
              instrs
          in
          let pairs = List.map (fun c -> (Node.make (), c)) cmds in
          let first, _ = List.nth pairs 0 in
          let last, _ = List.nth pairs (List.length pairs - 1) in
          let preds, succs = (pred n g, succ n g) in
          g
          |> (fun g ->
               (* add nodes in instrs *)
               List.fold_left (fun g (n, c) -> add_node_with_cmd n c g) g pairs)
          |> (fun g ->
               (* connect edges between instrs *)
               fst
                 (List.fold_left
                    (fun (g, p) (n, _) -> (add_edge p n g, n))
                    (g, n) pairs))
          |> list_fold (fun p -> add_edge p first) preds
          |> list_fold (fun s -> add_edge last s) succs
          |> remove_node n
      | Cmd.Cinstr ([], loc) ->
          if Cil.compareLoc loc Cil.locUnknown = 0 then
            let pred_locs =
              pred n g
              |> List.map (fun n -> find_cmd n g |> Cmd.location_of)
              |> List.filter (fun loc -> Cil.compareLoc loc Cil.locUnknown <> 0)
            in
            if pred_locs = [] then
              add_cmd n (Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)) g
            else add_cmd n (Cmd.Cskip (Cmd.Unknown, List.nth pred_locs 0)) g
          else add_cmd n (Cmd.Cskip (Cmd.Unknown, loc)) g
      | _ -> g)
    g g

let make_array lv typ exp local loc entry g =
  let alloc_node = Node.make () in
  let size = Cil.BinOp (Cil.Mult, Cil.SizeOf typ, exp, Cil.intType) in
  let alloc_cmd = Cmd.Calloc (lv, Cmd.Array size, local, true, loc) in
  (alloc_node, g |> add_cmd alloc_node alloc_cmd |> add_edge entry alloc_node)

let make_struct lv comp local loc entry g =
  let alloc_node = Node.make () in
  let alloc_cmd = Cmd.Calloc (lv, Cmd.Struct comp, local, true, loc) in
  (alloc_node, g |> add_cmd alloc_node alloc_cmd |> add_edge entry alloc_node)

let make_init_loop fd lv exp loc entry f g =
  (* i = 0 *)
  let init_node = Node.make () in
  let idxinfo = Cil.makeTempVar fd (Cil.TInt (IInt, [])) in
  let idx = (Cil.Var idxinfo, Cil.NoOffset) in
  let init_value = Cil.Const (Cil.CInt64 (Z.zero, IInt, None)) in
  let init_cmd = Cmd.Cset (idx, init_value, loc) in
  let g = add_cmd init_node init_cmd g in
  (* while (i < exp) *)
  let skip_node = Node.make () in
  let g = add_cmd skip_node (Cmd.Cskip (Cmd.LoopHead, loc)) g in
  let g = add_edge init_node skip_node g in
  let g = add_edge entry init_node g in
  let assume_node = Node.make () in
  let cond = Cil.BinOp (Cil.Lt, Cil.Lval idx, exp, Cil.intType) in
  let assume_cmd = Cmd.Cassume (cond, true, loc) in
  let g = add_cmd assume_node assume_cmd g in
  let g = add_edge skip_node assume_node g in
  let nassume_node = Node.make () in
  let nassume_cmd =
    Cmd.Cassume (Cil.UnOp (Cil.LNot, cond, Cil.intType), false, loc)
  in
  let g = add_cmd nassume_node nassume_cmd g in
  let g = add_edge skip_node nassume_node g in
  let element =
    Cil.addOffsetLval (Index (Lval (Var idxinfo, NoOffset), NoOffset)) lv
  in
  (* loop body *)
  let term, g = f assume_node element g in
  (* i++ *)
  let incr_node = Node.make () in
  let incr_cmd =
    Cmd.Cset
      ( idx,
        Cil.BinOp
          ( Cil.PlusA,
            Cil.Lval idx,
            Cil.Const (Cil.CInt64 (Z.one, IInt, None)),
            Cil.intType ),
        loc )
  in
  let g = add_cmd incr_node incr_cmd g in
  let g = add_edge term incr_node g in
  let g = add_edge incr_node skip_node g in
  (nassume_node, g)

let rec make_nested_array fd lv typ exp local loc entry initialize g =
  let typ = unrollTypeDeep typ in
  match typ with
  | TArray (t, Some size, _) ->
      let f assume_node element g =
        (* tmp = malloc(size); lv[i] = tmp *)
        let tmp =
          ( Cil.Var (Cil.makeTempVar fd (Cil.TPtr (Cil.TVoid [], []))),
            Cil.NoOffset )
        in
        let term, g = make_array tmp t size local loc assume_node g in
        let cast_node = Node.make () in
        let cast_cmd =
          Cmd.Cset (element, Cil.CastE (TPtr (t, []), Cil.Lval tmp), loc)
        in
        let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
        make_nested_array fd element t size local loc cast_node initialize g
      in
      make_init_loop fd lv exp loc entry f g
  | TComp (comp, _) ->
      let f assume_node element g =
        (* tmp = malloc(size); lv[i] = tmp *)
        let term, g = make_struct element comp local loc assume_node g in
        generate_allocs_field comp.cfields element local fd term g
      in
      make_init_loop fd lv exp loc entry f g
  | _ when initialize ->
      let f assume_node element g =
        (* lv[i] = 0 *)
        let init_node = Node.make () in
        let init_cmd = Cmd.Cset (element, Cil.zero, loc) in
        ( init_node,
          g |> add_cmd init_node init_cmd |> add_edge assume_node init_node )
      in
      make_init_loop fd lv exp loc entry f g
  | _ -> (entry, g)

and generate_allocs_field fl lv local fd entry g =
  match fl with
  | [] -> (entry, g)
  | fieldinfo :: t -> (
      match Cil.unrollTypeDeep fieldinfo.ftype with
      | TArray (typ, Some exp, _) ->
          let field = addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv in
          let tmp =
            (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
          in
          let term, g = make_array tmp typ exp local fieldinfo.floc entry g in
          let cast_node = Node.make () in
          let cast_cmd =
            Cmd.Cset
              ( field,
                Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp),
                fieldinfo.floc )
          in
          let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
          let term, g =
            make_nested_array fd field typ exp local fieldinfo.floc cast_node
              false g
          in
          generate_allocs_field t lv local fd term g
      | TComp (comp, _) ->
          let field = addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv in
          let term, g = make_struct field comp local fieldinfo.floc entry g in
          let term, g =
            generate_allocs_field comp.cfields field local fd term g
          in
          generate_allocs_field t lv local fd term g
      | _ -> generate_allocs_field t lv local fd entry g)

and get_base_type = function
  | TArray (t, _, _) | TPtr (t, _) -> get_base_type t
  | typ -> typ

let rec generate_local_allocs fd vl entry g =
  match vl with
  | [] -> (entry, g)
  | varinfo :: t -> (
      match Cil.unrollTypeDeep varinfo.vtype with
      | TArray (typ, Some exp, _) ->
          let lv = (Cil.Var varinfo, Cil.NoOffset) in
          let tmp =
            (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
          in
          let term, g = make_array tmp typ exp true varinfo.vdecl entry g in
          let cast_node = Node.make () in
          let cast_cmd =
            Cmd.Cset
              ( lv,
                Cil.CastE (Cil.TPtr (unrollTypeDeep typ, []), Cil.Lval tmp),
                varinfo.vdecl )
          in
          let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
          let term, g =
            make_nested_array fd lv typ exp true varinfo.vdecl cast_node false g
          in
          generate_local_allocs fd t term g
      | TComp (comp, _) ->
          let lv = (Cil.Var varinfo, Cil.NoOffset) in
          let term, g = make_struct lv comp true varinfo.vdecl entry g in
          let term, g = generate_allocs_field comp.cfields lv true fd term g in
          generate_local_allocs fd t term g
      | _ -> generate_local_allocs fd t entry g)

let replace_node_graph old entry exit g =
  let preds = pred old g in
  let succs = succ old g in
  let g = remove_node old g in
  let g = List.fold_left (fun g p -> add_edge p entry g) g preds in
  let g = List.fold_left (fun g s -> add_edge exit s g) g succs in
  g

(* string allocation  *)
let transform_string_allocs fd g =
  let rec replace_str e =
    match e with
    | Const (CStr s) ->
        let tempinfo =
          Cil.makeTempVar fd (Cil.TPtr (Cil.TInt (IChar, []), []))
        in
        let temp = (Cil.Var tempinfo, Cil.NoOffset) in
        (Lval temp, [ (temp, s) ])
    | Lval (Mem exp, off) -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (Lval (Mem exp', off), l))
    | SizeOfStr s ->
        let tempinfo =
          Cil.makeTempVar fd (Cil.TPtr (Cil.TInt (IChar, []), []))
        in
        let temp = (Cil.Var tempinfo, Cil.NoOffset) in
        (Lval temp, [ (temp, s) ])
    | SizeOfE exp -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (SizeOfE exp', l))
    | AlignOfE exp -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (AlignOfE exp', l))
    | UnOp (u, exp, t) -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (UnOp (u, exp', t), l))
    | BinOp (b, e1, e2, t) -> (
        let e1', l1 = replace_str e1 in
        let e2', l2 = replace_str e2 in
        match l1 @ l2 with
        | [] -> (e, [])
        | _ -> (BinOp (b, e1', e2', t), l1 @ l2))
    | CastE (t, exp) -> (
        let exp', l = replace_str exp in
        match l with [] -> (e, l) | _ -> (CastE (t, exp'), l))
    | _ -> (e, [])
  in
  let generate_sallocs l loc node g =
    List.fold_left
      (fun (node, g) (lv, s) ->
        let new_node = Node.make () in
        let g = add_edge node new_node g in
        let cmd = Cmd.Csalloc (lv, s, loc) in
        let g = add_cmd new_node cmd g in
        (new_node, g))
      (node, g) l
  in
  (* make it consistent with manual encoding in *Sem.ml *)
  let targets =
    [
      "strcpy";
      "strcat";
      "strncpy";
      "memcpy";
      "memmove";
      "strlen";
      "fgets";
      "sprintf";
      "scanf";
      "getenv";
      "strdup";
      "gettext";
      "getpwent";
      "strchr";
      "strrchr";
    ]
  in
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Cset (lv, e, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Cset (lv, e, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | Cmd.Cassume (e, b, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Cassume (e, b, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      (* do not allocate memory cells for arguments of external lib calls *)
      | Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, _)
        when f.vstorage = Cil.Extern && not (List.mem f.vname targets) ->
          g
      | Cmd.Ccall (lv, f, el, loc) -> (
          let el, l =
            List.fold_left
              (fun (el, l) param ->
                let e', l' = replace_str param in
                (el @ [ e' ], l @ l'))
              ([], []) el
          in
          match (el, l) with
          | _, [] -> g
          | el, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Ccall (lv, f, el, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | Cmd.Creturn (Some e, loc) -> (
          match replace_str e with
          | _, [] -> g
          | e, l ->
              let empty_node, last_node = (Node.make (), Node.make ()) in
              let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
              let node, g = generate_sallocs l loc empty_node g in
              let cmd = Cmd.Creturn (Some e, loc) in
              let g = add_cmd last_node cmd g in
              let g = add_edge node last_node g in
              replace_node_graph n empty_node last_node g)
      | _ -> g)
    g g

(** transform malloc to Calloc *)
let transform_malloc fd g =
  let rec transform lv exp loc node g =
    match exp with
    (* TODO: For tricky PlusA patterns, fall back to the lvalue type. Note that
     * a simple code transformation must be preceded. This is because CIL first
     * assigns the return of malloc() into a temorary variable with void pointer
     * and then casts it to the actual pointer variable in the program. *)
    | BinOp (Mult, SizeOf typ, e, _)
    | BinOp (Mult, e, SizeOf typ, _)
    | BinOp (Mult, CastE (_, SizeOf typ), e, _)
    | BinOp (Mult, e, CastE (_, SizeOf typ), _) -> (
        let typ = Cil.unrollTypeDeep typ in
        match (lv, typ) with
        | (Var _, NoOffset), TComp (_, _) ->
            (* dynamic struct array alloc *)
            let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
            let g = add_cmd node cmd g in
            make_nested_array fd lv typ e false loc node false g
        | _ ->
            let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
            let g = add_cmd node cmd g in
            (node, g))
    | BinOp (Mult, SizeOfE ex1, ex2, t)
    | BinOp (Mult, ex2, SizeOfE ex1, t)
    | BinOp (Mult, CastE (_, SizeOfE ex1), ex2, t)
    | BinOp (Mult, ex2, CastE (_, SizeOfE ex1), t) ->
        transform lv (BinOp (Mult, SizeOf (Cil.typeOf ex1), ex2, t)) loc node g
    (* We often observe the case of "S* s = malloc(sizeof(S) + n)" *)
    | BinOp (PlusA, SizeOf typ, _, _)
    | BinOp (PlusA, CastE (_, SizeOf typ), _, _) ->
        transform lv (SizeOf typ) loc node g
    | BinOp (PlusA, SizeOfE ex1, _, _)
    | BinOp (PlusA, CastE (_, SizeOfE ex1), _, _) ->
        transform lv (SizeOf (Cil.typeOf ex1)) loc node g
    | SizeOf typ | CastE (_, SizeOf typ) -> (
        let typ = Cil.unrollTypeDeep typ in
        match (lv, typ) with
        | (Var _, NoOffset), TComp (comp, _) ->
            (* dynamic struct alloc *)
            let cast_node = Node.make () in
            let cast_cmd =
              Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval lv), loc)
            in
            let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
            g |> add_cmd node cmd |> add_cmd cast_node cast_cmd
            |> add_edge node cast_node
            |> generate_allocs_field comp.cfields (Mem (Lval lv), NoOffset)
                 false fd cast_node
        | _, _ ->
            let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
            let g = add_cmd node cmd g in
            (node, g))
    | SizeOfE e | CastE (_, SizeOfE e) ->
        transform lv (SizeOf (Cil.typeOf e)) loc node g
    | CastE (_, e) -> transform lv e loc node g
    | _ ->
        let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
        let g = add_cmd node cmd g in
        (node, g)
  in
  let try_resolve_alloc_size fname args =
    match (fname, args) with
    | "malloc", size :: _ | "__builtin_alloca", size :: _ -> Some size
    | "realloc", _ :: size :: _ -> Some size
    | "calloc", n :: size :: _ -> Some (BinOp (Mult, n, size, Cil.uintType))
    | _, _ -> None
  in
  fold_node
    (fun n g ->
      match find_cmd n g with
      | Cmd.Ccall (Some lv, Lval (Var varinfo, NoOffset), args, loc) -> (
          match try_resolve_alloc_size varinfo.vname args with
          | Some arg ->
              let new_node = Node.make () in
              let preds = pred n g in
              let succs = succ n g in
              let g = List.fold_left (fun g s -> remove_edge n s g) g succs in
              let g = List.fold_left (fun g p -> remove_edge p n g) g preds in
              let g = remove_node n g in
              let g =
                List.fold_left (fun g p -> add_edge p new_node g) g preds
              in
              let lv =
                match lv with
                | Var v, NoOffset ->
                    (Var { v with vtype = voidPtrType }, NoOffset)
                | _ -> lv
              in
              let term, g = transform lv arg loc new_node g in
              List.fold_left (fun g s -> add_edge term s g) g succs
          | None -> g)
      | _ -> g)
    g g

(** for each call-node, insert a corresponding return-node *)
let insert_return_nodes g =
  List.fold_left
    (fun g c ->
      match find_cmd c g with
      | Cmd.Ccall (_, Lval (Var varinfo, _), _, loc)
        when varinfo.vname = "exit" || varinfo.vname = "abort"
             || Cil.hasAttribute "noreturn" varinfo.vattr ->
          let r = return_of c g in
          let n = Node.make () in
          remove_edge c r g
          |> add_cmd n (Cmd.Cskip (Cmd.ReturnNode, loc))
          |> add_edge c n
      | Cmd.Ccall (_, _, _, loc) ->
          let r = return_of c g in
          add_new_node c (Cmd.Cskip (Cmd.ReturnNode, loc)) r g
      | _ -> g)
    g (nodes_of g)

(** before each exit-node, insert a return cmd if there is not *)
let insert_return_before_exit g =
  let add_return node acc =
    match find_cmd node g with
    | Cmd.Creturn _ -> acc
    | _ -> add_new_node node (Cmd.Creturn (None, locUnknown)) Node.EXIT acc
  in
  list_fold add_return (pred Node.EXIT g) g

let compute_dom g =
  let dom_functions = Dom.compute_all (GDom.fromG g.graph) Node.ENTRY in
  let dom_tree =
    List.fold_left
      (fun dom_tree node ->
        List.fold_left
          (fun dom_tree child -> G.add_edge dom_tree node child)
          dom_tree
          (dom_functions.Dom.dom_tree node))
      G.empty (nodes_of g)
  in
  let dom_fronts =
    List.fold_left
      (fun dom_fronts node ->
        BatMap.add node
          (NodeSet.of_list (dom_functions.Dom.dom_frontier node))
          dom_fronts)
      BatMap.empty (nodes_of g)
  in
  let post_dom_functions = Dom.compute_all (Oper.mirror g.graph) Node.EXIT in
  let post_dom_fronts =
    List.fold_left
      (fun post_dom_fronts node ->
        BatMap.add node
          (NodeSet.of_list (post_dom_functions.Dom.dom_frontier node))
          post_dom_fronts)
      BatMap.empty (nodes_of g)
  in
  { g with dom_tree; dom_fronts; post_dom_fronts }

let compute_scc g = { g with scc_list = Scc.scc_list g.graph }

let process_gvardecl fd lv init_opt loc entry g =
  match (Cil.unrollTypeDeep (Cil.typeOfLval lv), init_opt) with
  | TArray (typ, Some exp, _), _ ->
      let tmp = (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset) in
      let term, g = make_array tmp typ exp false loc entry g in
      let cast_node = Node.make () in
      let cast_cmd =
        Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp), loc)
      in
      let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
      let term, g =
        make_nested_array fd lv typ exp false loc cast_node true g
      in
      (term, g)
  | TArray (typ, None, _), Some ilist ->
      (* For example, int arr[] = {1,2,3}. CIL generates "int arr[3] = ..." while Clang generates "int arr[] = ..." *)
      let tmp = (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset) in
      let exp = List.length ilist |> Cil.integer in
      let term, g = make_array tmp typ exp false loc entry g in
      let cast_node = Node.make () in
      let cast_cmd =
        Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp), loc)
      in
      let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
      let term, g =
        make_nested_array fd lv typ exp false loc cast_node true g
      in
      (term, g)
  | TInt (_, _), _ | TFloat (_, _), _ ->
      let node = Node.make () in
      let cmd = Cmd.Cset (lv, Cil.zero, loc) in
      (node, g |> add_cmd node cmd |> add_edge entry node)
  | TComp (comp, _), _ ->
      let term, g = make_struct lv comp false loc entry g in
      let term, g = generate_allocs_field comp.cfields lv false fd term g in
      (term, g)
  | _ -> (entry, g)

let rec process_init fd lv i loc entry g =
  match i with
  | SingleInit exp ->
      let new_node = Node.make () in
      let cmd = Cmd.Cset (lv, exp, loc) in
      let g = add_edge entry new_node (add_cmd new_node cmd g) in
      (new_node, g)
  | CompoundInit (_, ilist) ->
      List.fold_left
        (fun (node, g) (offset, init) ->
          let lv = Cil.addOffsetLval offset lv in
          process_init fd lv init loc node g)
        (entry, g) ilist

let process_gvar fd lv i loc entry g =
  match (Cil.typeOfLval lv, i.init) with
  | _, None ->
      process_gvardecl fd lv None loc entry g (* e.g., int global;     *)
  | _, Some (SingleInit _ as init) ->
      (* e.g., int global = 1; *)
      process_init fd lv init loc entry g
  | _, Some (CompoundInit (_, ilist) as init) ->
      (* e.g., int global = { 1, 2 }; *)
      let length = List.length ilist in
      if length > 1000 then
        Logging.warn "WARN: too large global array initialization (%d) %@ %s\n"
          (List.length ilist) (CilHelper.s_location loc);
      let node, g = process_gvardecl fd lv (Some ilist) loc entry g in
      if length < !Options.unsound_skip_global_array_init then
        process_init fd lv init loc node g
      else (node, g)

let get_main_dec globals =
  List.fold_left
    (fun s g ->
      match g with
      | Cil.GFun (fundec, loc) when fundec.svar.vname = !Options.entry_point ->
          Some (fundec, loc)
      | _ -> s)
    None globals

let process_fundecl fundecl loc node g =
  let new_node = Node.make () in
  let cmd = Cmd.Cfalloc ((Var fundecl.svar, NoOffset), fundecl, loc) in
  let g = add_edge node new_node (add_cmd new_node cmd g) in
  (new_node, g)

let generate_cmd_args fd loc g =
  let argc, argv =
    ( (Cil.Var (List.nth fd.sformals 0), Cil.NoOffset),
      (Cil.Var (List.nth fd.sformals 1), Cil.NoOffset) )
  in
  let arg_node = Node.make () in
  let arg_cmd =
    Cmd.Ccall
      ( None,
        Cil.Lval
          (Cil.Var (Cil.makeGlobalVar "sparrow_arg" Cil.voidType), Cil.NoOffset),
        [ Cil.Lval argc; Cil.Lval argv ],
        loc )
  in
  let optind, optarg =
    ( (Cil.Var (Cil.makeGlobalVar "optind" Cil.intType), Cil.NoOffset),
      (Cil.Var (Cil.makeGlobalVar "optarg" Cil.charPtrType), Cil.NoOffset) )
  in
  let opt_node = Node.make () in
  let opt_cmd =
    Cmd.Ccall
      ( None,
        Cil.Lval
          (Cil.Var (Cil.makeGlobalVar "sparrow_opt" Cil.voidType), Cil.NoOffset),
        [ Cil.Lval optind; Cil.Lval optarg ],
        loc )
  in
  let g =
    g |> add_cmd arg_node arg_cmd |> add_cmd opt_node opt_cmd
    |> add_edge Node.ENTRY arg_node
    |> add_edge arg_node opt_node
  in
  (opt_node, g)

let ignore_function fd =
  List.map
    (fun str -> Str.regexp (".*" ^ str ^ ".*"))
    !Options.unsound_skip_function
  |> List.exists (fun re -> Str.string_match re fd.svar.vname 0)

let init fd loc =
  let g =
    empty fd
    |> add_node_with_cmd Node.ENTRY (Cmd.Cskip (Cmd.Unknown, loc))
    |> add_node_with_cmd Node.EXIT (Cmd.Cskip (Cmd.Unknown, loc))
  in
  if
    !Options.unsound_noreturn_function
    && Cil.hasAttribute "noreturn" fd.svar.vattr
    || ignore_function fd
  then add_edge Node.ENTRY Node.EXIT g
  else
    let entry = Node.fromCilStmt (List.nth fd.sallstmts 0) in
    let g =
      (* add nodes *)
      (list_fold
         (fun s ->
           add_node_with_cmd (Node.fromCilStmt s) (Cmd.fromCilStmt s.skind))
         fd.sallstmts
      >>> (* add edges *)
      list_fold
        (fun stmt ->
          list_fold
            (fun succ ->
              add_edge (Node.fromCilStmt stmt) (Node.fromCilStmt succ))
            stmt.succs)
        fd.sallstmts)
        g
    in
    let term, g =
      if fd.svar.vname = "main" && List.length fd.sformals >= 2 then
        generate_cmd_args fd loc g
      else (Node.ENTRY, g)
    in
    (* generate alloc cmds for static allocations *)
    let term, g = generate_local_allocs fd fd.slocals term g in
    let g = add_edge term entry g in
    let nodes = nodes_of g in
    let lasts = List.filter (fun n -> succ n g = []) nodes in
    g
    |> list_fold
         (function Node.EXIT -> id | last -> add_edge last Node.EXIT)
         lasts
    |> generate_assumes |> flatten_instructions |> remove_if_loop
    |> transform_malloc fd
    (* generate alloc cmds for dynamic allocations *)
    |> transform_string_allocs fd
    (* generate salloc (string alloc) cmds *)
    |> remove_empty_nodes
    |> insert_return_nodes |> insert_return_before_exit

let ignore_file regexps loc =
  List.exists (fun re -> Str.string_match re loc.file 0) regexps

let generate_global_proc globals fd =
  let entry = Node.ENTRY in
  let regexps =
    List.map
      (fun str -> Str.regexp (".*" ^ str ^ ".*"))
      !Options.unsound_skip_file
  in
  let term, g =
    List.fold_left
      (fun (node, g) x ->
        match x with
        | Cil.GVar (var, init, loc) when not (ignore_file regexps loc) ->
            process_gvar fd (Cil.var var) init loc node g
        | Cil.GVarDecl (var, loc) when not (ignore_file regexps loc) ->
            process_gvardecl fd (Cil.var var) None loc node g
        | Cil.GFun (fundec, loc) when not (ignore_file regexps loc) ->
            process_fundecl fundec loc node g
        | _ -> (node, g))
      (entry, empty fd)
      globals
  in
  let add_call_main g =
    match get_main_dec globals with
    | Some (main_dec, main_loc) ->
        let call_node = Node.make () in
        let call_cmd =
          Cmd.Ccall (None, Lval (Var main_dec.svar, NoOffset), [], main_loc)
        in
        g |> add_cmd call_node call_cmd |> add_edge term call_node
        |> add_edge call_node Node.EXIT
    | None ->
        prerr_endline "Warning: main not Found";
        g |> add_edge term Node.EXIT
  in
  g |> add_call_main |> generate_assumes |> flatten_instructions
  |> remove_if_loop |> transform_string_allocs fd
  (* generate salloc (string alloc) cmds *)
  |> remove_empty_nodes
  |> insert_return_nodes

let unreachable_node g =
  let all_nodes = NodeSet.of_list (nodes_of g) in
  let rec remove_reachable_node' work acc =
    if NodeSet.is_empty work then acc
    else
      let node, work = NodeSet.pop work in
      if NodeSet.mem node acc then
        let acc = NodeSet.remove node acc in
        let succs = NodeSet.remove node (NodeSet.of_list (succ node g)) in
        let work = NodeSet.union work succs in
        remove_reachable_node' work acc
      else remove_reachable_node' work acc
  in
  remove_reachable_node' (NodeSet.singleton Node.ENTRY) all_nodes

let merge_vertex g vl =
  { g with graph = Merge.merge_vertex g.graph vl }
  |> remove_edge (List.hd vl) (List.hd vl)

let rec collect g n lval node_list exp_list =
  let s = succ n g |> List.hd in
  match (find_cmd n g, find_cmd s g) with
  | Cmd.Csalloc (_, str, _), Cmd.Cset (l, _, _) -> (
      match Cil.removeOffsetLval l with
      | l, Cil.Index (i, Cil.NoOffset)
        when CilHelper.eq_lval lval l && Cil.isConstant i ->
          let node_list, exp_list =
            (n :: s :: node_list, Cil.mkString str :: exp_list)
          in
          let ss = succ s g in
          if List.length ss = 1 then
            collect g (List.hd ss) lval node_list exp_list
          else (node_list, exp_list)
      | _ -> (node_list, exp_list))
  | Cmd.Cset (l, e, _), _ when Cil.isConstant e -> (
      match Cil.removeOffsetLval l with
      | l, Cil.Index (i, Cil.NoOffset)
        when CilHelper.eq_lval lval l && Cil.isConstant i ->
          let node_list, exp_list = (n :: node_list, e :: exp_list) in
          let ss = succ n g in
          if List.length ss = 1 then
            collect g (List.hd ss) lval node_list exp_list
          else (node_list, exp_list)
      | _ -> (node_list, exp_list))
  | _ -> (node_list, exp_list)

let is_candidate n g =
  let is_starting_point lval =
    match Cil.removeOffsetLval lval with
    | l, Cil.Index (i, Cil.NoOffset) when Cil.isZero i -> Some l
    | _ -> None
  in
  let ss = try succ n g with _ -> [] in
  if List.length ss = 1 then
    let s = List.hd ss in
    match (find_cmd n g, find_cmd s g) with
    | Cmd.Csalloc (_, _, _), Cmd.Cset (lval, e, _)
      when Cil.isPointerType (Cil.typeOf e) ->
        is_starting_point lval
    | Cmd.Cset (lval, e, _), _ when Cil.isIntegralType (Cil.typeOf e) ->
        is_starting_point lval
    | _ -> None
  else None

(* arr[0] = c0; arr[1] = c1; ..., arr[n] = cn; => sparrow_array_init(arr,c0, c1, ..., cn);
   salloc(arr[0], x0); x0 = s0; ..., => sparrow_array_init(arr, s0, s1, ..., sn) *)
let optimize_array_init g =
  fold_node
    (fun n g ->
      match is_candidate n g with
      | Some lval ->
          let nodes, exps = collect g n lval [] [] in
          if List.length nodes > 1 then
            let new_node = Node.make () in
            let g = merge_vertex g (new_node :: nodes) in
            let args = Cil.Lval lval :: List.rev exps in
            let loc = find_cmd n g |> Cmd.location_of in
            let cmd =
              Cmd.Ccall
                ( None,
                  Cil.Lval
                    ( Cil.Var
                        (Cil.makeGlobalVar "sparrow_array_init" Cil.voidType),
                      Cil.NoOffset ),
                  args,
                  loc )
            in
            add_cmd new_node cmd g
          else g
      | _ -> g)
    g g

let optimize = optimize_array_init

let print_dot chan g =
  let open Printf in
  fprintf chan "digraph %s {\n" g.fd.svar.vname;
  fprintf chan "{\n";
  fprintf chan "node [shape=box]\n";
  G.iter_vertex
    (fun v ->
      fprintf chan "%s [label=\"%s: %s\" %s]\n" (Node.to_string v)
        (Node.to_string v)
        (Cmd.to_string (find_cmd v g))
        (if is_call_node v g then "style=filled color=grey" else ""))
    g.graph;
  fprintf chan "}\n";
  G.iter_edges
    (fun v1 v2 ->
      fprintf chan "%s -> %s\n" (Node.to_string v1) (Node.to_string v2))
    g.graph;
  fprintf chan "}\n"

let print_dom_fronts dom_fronts =
  BatMap.iter
    (fun node fronts ->
      prerr_string (Node.to_string node ^ ": ");
      NodeSet.iter (fun fr -> prerr_string (Node.to_string fr ^ " ")) fronts;
      prerr_endline "")
    dom_fronts

let print_dom_tree dom_tree =
  prerr_endline (string_of_map Node.to_string Node.to_string dom_tree)

module Json = Yojson.Safe

let nodes_to_json g =
  G.fold_vertex
    (fun v nodes ->
      let node_id = Node.to_string v in
      let instr = find_cmd v g |> Cmd.to_string in
      let is_call_node = is_call_node v g in
      let attrs = `List [ `String instr; `Bool false; `Bool is_call_node ] in
      (node_id, attrs) :: nodes)
    g.graph []
  |> fun x -> `Assoc x

let edges_to_json g =
  G.fold_edges
    (fun v1 v2 edges ->
      let nid1 = Node.to_string v1 in
      let nid2 = Node.to_string v2 in
      `List [ `String nid1; `String nid2 ] :: edges)
    g.graph []
  |> fun x -> `List x

let dom_fronts_to_json g =
  BatMap.foldi
    (fun v1 set edges ->
      let nid1 = Node.to_string v1 in
      NodeSet.fold
        (fun v2 edges ->
          let nid2 = Node.to_string v2 in
          let p = `List [ `String nid1; `String nid2 ] in
          p :: edges)
        set edges)
    g.dom_fronts []
  |> fun x -> `List x

let control_dep_to_json g =
  BatMap.foldi
    (fun v1 set edges ->
      let nid1 = Node.to_string v1 in
      NodeSet.fold
        (fun v2 edges ->
          let nid2 = Node.to_string v2 in
          let p = `List [ `String nid1; `String nid2 ] in
          p :: edges)
        set edges)
    g.post_dom_fronts []
  |> fun x -> `List x

let to_json g =
  let nodes = nodes_to_json g in
  let edges = edges_to_json g in
  let dom_fronts = dom_fronts_to_json g in
  let control_dep = control_dep_to_json g in
  `Assoc
    [
      ("nodes", nodes);
      ("edges", edges);
      ("dom_fronts", dom_fronts);
      ("control_dep", control_dep);
    ]

let nodes_to_json_simple g =
  G.fold_vertex
    (fun v l ->
      let cmd = find_cmd v g in
      let loc = Cmd.location_of cmd |> CilHelper.s_location in
      let item = `Assoc [ ("cmd", Cmd.to_json cmd); ("loc", `String loc) ] in
      (g.fd.svar.vname ^ "-" ^ Node.to_string v, item) :: l)
    g.graph []
  |> fun x -> `Assoc x

let edges_to_json_simple g =
  G.fold_edges
    (fun v1 v2 edges ->
      `List
        [
          `String (pid g ^ "-" ^ Node.to_string v1);
          `String (pid g ^ "-" ^ Node.to_string v2);
        ]
      :: edges)
    g.graph []
  |> fun x -> `List x

let to_json_simple g =
  let nodes = nodes_to_json g in
  let edges = edges_to_json g in
  `Assoc [ ("nodes", nodes); ("edges", edges) ]
