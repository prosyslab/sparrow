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
open BasicDom
open AbsSem
module L = Logging

let total_iterations = ref 0
let g_clock = ref 0.0
let l_clock = ref 0.0

module type S = sig
  module Dom : InstrumentedMem.S

  module Table :
    MapDom.CPO
      with type t = MapDom.MakeCPO(BasicDom.Node)(Dom).t
       and type A.t = BasicDom.Node.t
       and type B.t = Dom.t

  module DUGraph : Dug.S with type PowLoc.t = Dom.PowA.t

  module Spec :
    Spec.S
      with type Dom.t = Dom.t
       and type Dom.A.t = Dom.A.t
       and type Dom.PowA.t = Dom.PowA.t

  val generate_dug : Spec.t -> Global.t -> DUGraph.t
  val to_json : Global.t * DUGraph.t -> Yojson.Safe.t

  val perform :
    Spec.t -> Global.t -> DUGraph.t -> Global.t * DUGraph.t * Table.t * Table.t
end

module MakeWithAccess (Sem : AccessSem.S) = struct
  module Dom = Sem.Dom
  module AccessAnalysis = AccessAnalysis.Make (Sem)
  module Access = AccessAnalysis.Access
  module DUGraph = Dug.Make (Access)
  module SsaDug = SsaDug.Make (DUGraph)
  module Worklist = Worklist.Make (DUGraph)
  module Table = MapDom.MakeCPO (Node) (Sem.Dom)
  module Spec = Sem.Spec
  module PowLoc = Sem.Dom.PowA

  let needwidening idx wl = Worklist.is_loopheader idx wl
  let def_locs_cache = Hashtbl.create 251

  let get_def_locs idx dug =
    try Hashtbl.find def_locs_cache idx
    with Not_found ->
      let def_locs =
        let union_locs succ = PowLoc.union (DUGraph.get_abslocs idx succ dug) in
        DUGraph.fold_succ union_locs dug idx PowLoc.empty
      in
      Hashtbl.add def_locs_cache idx def_locs;
      def_locs

  let print_iteration () =
    total_iterations := !total_iterations + 1;
    if !total_iterations = 1 then (
      g_clock := Sys.time ();
      l_clock := Sys.time ())
    else if !total_iterations mod 10000 = 0 then (
      let g_time = Format.sprintf "%.2f" (Sys.time () -. !g_clock) in
      let l_time = Format.sprintf "%.2f" (Sys.time () -. !l_clock) in
      my_prerr_string
        ("\r#iters: "
        ^ string_of_int !total_iterations
        ^ " took " ^ g_time ^ "s  (" ^ l_time ^ "s / last 10000 iters)");
      flush stderr;
      l_clock := Sys.time ())

  let propagate dug idx (works, inputof, outputof)
      (unstables, new_output, global) =
    let works, inputof =
      let update_succ succ (works, inputof) =
        let old_input = Table.find succ inputof in
        let locs_on_edge = DUGraph.get_abslocs idx succ dug in
        let is_on_edge (x, _) = DUGraph.mem_duset x locs_on_edge in
        let to_join = List.filter is_on_edge unstables in
        if to_join = [] then (works, inputof)
        else
          let new_input = Dom.join_pairs to_join old_input in
          (Worklist.push idx succ works, Table.add succ new_input inputof)
      in
      DUGraph.fold_succ update_succ dug idx (works, inputof)
    in
    (works, global, inputof, Table.add idx new_output outputof)

  let get_unstable dug idx works old_output (new_output, global) =
    let def_locs =
      Profiler.event "SparseAnalysis.widening_get_def_locs" (get_def_locs idx)
        dug
    in
    let is_unstb v1 v2 = not (Dom.B.le v2 v1) in
    let u =
      Profiler.event "SparseAnalysis.widening_unstable"
        (Dom.unstables old_output new_output is_unstb)
        def_locs
    in
    if u = [] then None
    else
      let op = if needwidening idx works then Dom.B.widen else fun _ y -> y in
      let _ = Profiler.start_event "SparseAnalysis.widening_new_output" in
      let u = List.map (fun (k, v1, v2) -> (k, op v1 v2)) u in
      let new_output = list_fold (fun (k, v) -> Dom.add k v) u old_output in
      let _ = Profiler.finish_event "SparseAnalysis.widening_new_output" in
      (* update unstable locations's values by widened values *)
      let u = List.map (fun (k, _) -> (k, Dom.find k new_output)) u in
      Some (u, new_output, global)

  let prdbg_input node (mem, global) =
    prerr_endline (Node.to_string node);
    prerr_endline (IntraCfg.Cmd.to_string (InterCfg.cmd_of global.icfg node));
    prerr_endline "== Input ==";
    prerr_endline (Dom.to_string mem);
    (mem, global)

  let prdbg_output old_output (new_output, global) =
    prerr_endline "== Old Output ==";
    prerr_endline (Dom.to_string old_output);
    prerr_endline "== New Output ==";
    prerr_endline (Dom.to_string new_output);
    (new_output, global)

  (* fixpoint iterator specialized to the widening phase *)
  let analyze_node spec dug idx (works, global, inputof, outputof) =
    print_iteration ();
    let old_output = Table.find idx outputof in
    (Table.find idx inputof, global)
    |> opt !Options.debug (prdbg_input idx)
    |> Profiler.event "SparseAnalysis.run" (Sem.run Strong spec idx)
    |> opt !Options.debug (prdbg_output old_output)
    |> Profiler.event "SparseAnalysis.get_unstable"
         (get_unstable dug idx works old_output)
    &> Profiler.event "SparseAnalysis.propagating"
         (propagate dug idx (works, inputof, outputof))
    |> function
    | None -> (works, global, inputof, outputof)
    | Some x -> x

  (* fixpoint iterator that can be used in both widening and narrowing phases *)
  let analyze_node_with_otable (widen, order) spec dug idx
      (works, global, inputof, outputof) =
    print_iteration ();
    let pred = DUGraph.pred idx dug in
    let input =
      List.fold_left
        (fun m p ->
          let pmem = Table.find p outputof in
          let locs_on_edge = DUGraph.get_abslocs p idx dug in
          PowLoc.fold
            (fun l m ->
              let v1 = Dom.find l pmem in
              let v2 = Dom.find l m in
              Dom.add l (Dom.B.join v1 v2) m)
            locs_on_edge m)
        Dom.bot pred
    in
    let inputof = Table.add idx input inputof in
    let old_output = Table.find idx outputof in
    let new_output, global = Sem.run Strong spec idx (input, global) in
    let widened = widen old_output new_output in
    if order widened old_output then (works, global, inputof, outputof)
    else
      let works =
        Worklist.push_set idx (BatSet.of_list (DUGraph.succ idx dug)) works
      in
      (works, global, inputof, Table.add idx new_output outputof)

  let rec iterate f dug (works, global, inputof, outputof) =
    match Worklist.pick works with
    | None -> (works, global, inputof, outputof)
    | Some (idx, rest) ->
        (rest, global, inputof, outputof) |> f dug idx |> iterate f dug

  let widening spec dug (worklist, global, inputof, outputof) =
    total_iterations := 0;
    ( worklist |> Worklist.push_set InterCfg.start_node (DUGraph.nodes_of dug)
    |> fun init_worklist ->
      iterate (analyze_node spec) dug (init_worklist, global, inputof, outputof)
    )
    |> fun x ->
    L.info ~level:1 "\n#iteration in widening : %d\n" !total_iterations;
    x

  let narrowing ?(initnodes = BatSet.empty) spec dug
      (worklist, global, inputof, outputof) =
    total_iterations := 0;
    ( worklist
    |> Worklist.push_set InterCfg.start_node
         (if BatSet.is_empty initnodes then DUGraph.nodes_of dug else initnodes)
    |> fun init_worklist ->
      iterate
        (analyze_node_with_otable (Dom.narrow, fun x y -> Dom.le y x) spec)
        dug
        (init_worklist, global, inputof, outputof) )
    |> fun x ->
    L.info ~level:1 "#iteration in narrowing : %d\n" !total_iterations;
    x

  let to_json (global, dug) =
    `Assoc
      [
        ("callgraph", CallGraph.to_json global.callgraph);
        ("cfgs", InterCfg.to_json global.icfg);
        ("dugraph", DUGraph.to_json dug)
        (*          ("dugraph-inter", DUGraph.to_json_inter dug access);*);
      ]

  let print_dug (global, dug) =
    if !Options.dug then (
      if DUGraph.nb_loc dug > 1000 then (
        L.info ~level:1
          "Too many abstract locations (> 1000) on DUG. Save as binary rather \
           than json.\n";
        let oc = open_out (Filename.concat !Options.outdir "dug.bin") in
        Marshal.to_channel oc dug [];
        close_out oc;
        let oc = open_out (Filename.concat !Options.outdir "global.bin") in
        Marshal.to_channel oc global [];
        close_out oc)
      else
        let oc = open_out (Filename.concat !Options.outdir "dug.json") in
        to_json (global, dug) |> Yojson.Safe.pretty_to_channel oc;
        close_out oc);
    prerr_memory_usage ();
    L.info "#Nodes in def-use graph : %d\n" (DUGraph.nb_node dug);
    L.info "#Locs on def-use graph : %d\n" (DUGraph.nb_loc dug)

  let bind_fi_locs mem_fi dug inputof =
    DUGraph.fold_node
      (fun n t ->
        let used =
          Access.Info.useof (Access.find_node n (DUGraph.access dug))
        in
        let pred = DUGraph.pred n dug in
        let locs_on_edge =
          list_fold
            (fun p -> PowLoc.union (DUGraph.get_abslocs p n dug))
            pred PowLoc.empty
        in
        let locs_not_on_edge = PowLoc.diff used locs_on_edge in
        let mem_with_locs_not_on_edge =
          PowLoc.fold
            (fun loc mem -> Dom.add loc (Dom.find loc mem_fi) mem)
            locs_not_on_edge (Table.find n inputof)
        in
        Table.add n mem_with_locs_not_on_edge t)
      dug inputof

  (* add pre-analysis memory to unanalyzed nodes *)
  let bind_unanalyzed_node global mem_fi dug inputof =
    let nodes = InterCfg.nodes_of global.icfg in
    let nodes_in_dug = DUGraph.nodes_of dug in
    list_fold
      (fun node t ->
        if BatSet.mem node nodes_in_dug then t
        else
          let mem_with_access =
            PowLoc.fold
              (fun loc -> Dom.add loc (Dom.find loc mem_fi))
              (Access.Info.useof (Access.find_node node (DUGraph.access dug)))
              Dom.bot
          in
          Table.add node mem_with_access t)
      nodes inputof

  let initialize spec dug =
    Table.add InterCfg.start_node (Sem.initial spec.Spec.locset) Table.empty
    |> cond (!Options.pfs < 100) (bind_fi_locs spec.Spec.premem dug) id

  let finalize spec dug (worklist, global, inputof, outputof) =
    let inputof =
      if !Options.pfs < 100 then
        bind_unanalyzed_node global spec.Spec.premem dug inputof
      else inputof
    in
    (worklist, global, inputof, outputof)

  let print_spec spec =
    L.info ~level:1 "#total abstract locations  = %d\n"
      (PowLoc.cardinal spec.Spec.locset);
    L.info ~level:1 "#flow-sensitive abstract locations  = %d\n"
      (PowLoc.cardinal spec.Spec.locset_fs)

  let generate_dug spec global =
    print_spec spec;
    let access =
      StepManager.stepf false "Access Analysis"
        (AccessAnalysis.perform global spec.Spec.locset (Sem.run Strong spec))
        spec.Spec.premem
    in
    let dug =
      StepManager.stepf false "Def-use graph construction" SsaDug.make
        (global, access, spec.Spec.locset_fs)
    in
    print_dug (global, dug);
    dug

  let perform spec global dug =
    let worklist =
      StepManager.stepf false "Workorder computation" Worklist.init dug
    in
    let dug =
      DUGraph.update_loopheads (Worklist.loopheads worklist) dug
      |> DUGraph.update_backedges (Worklist.backedges worklist)
    in
    (worklist, global, initialize spec dug, Table.empty)
    |> StepManager.stepf false "Fixpoint iteration with widening"
         (widening spec dug)
    |> finalize spec dug
    |> StepManager.stepf_opt !Options.narrow false
         "Fixpoint iteration with narrowing" (narrowing spec dug)
    |> fun (_, global, inputof, outputof) -> (global, dug, inputof, outputof)
end

module Make (Sem : AbsSem.S) = MakeWithAccess (AccessSem.Make (Sem))
