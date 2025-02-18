open Vocab
open AlarmExp
open BasicDom
open Global
open Report
module F = Format

let analysis = Spec.Taint

module Analysis = SparseAnalysis.Make (TaintSem)
module Table = Analysis.Table
module Spec = Analysis.Spec
module Mem = TaintDom.Mem

let marshal_in global =
  let filename = Filename.basename global.file.fileName in
  let global = MarshalManager.input (filename ^ ".taint.global") in
  let dug = MarshalManager.input (filename ^ ".taint.dug") in
  let input = MarshalManager.input (filename ^ ".taint.input") in
  let output = MarshalManager.input (filename ^ ".taint.output") in
  (global, dug, input, output)

let marshal_out (global, dug, input, output) =
  let filename = Filename.basename global.file.fileName in
  MarshalManager.output (filename ^ ".taint.global") global;
  MarshalManager.output (filename ^ ".taint.dug") dug;
  MarshalManager.output (filename ^ ".taint.input") input;
  MarshalManager.output (filename ^ ".taint.output") output;
  (global, dug, input, output)

let inspect_aexp_bo node aexp itvmem mem queries =
  match aexp with
  | AllocSize (_, e, loc) ->
      let pid = InterCfg.Node.pid node in
      let size_itv = ItvSem.eval pid e itvmem |> ItvDom.Val.itv_of_val in
      let taint = TaintSem.eval pid e itvmem mem |> TaintDom.Val.user_input in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let size_ovfl =
            TaintSem.eval pid e itvmem mem
            |> TaintDom.Val.int_overflow |> TaintDom.IntOverflow.is_bot |> not
          in
          let status =
            if size_ovfl && not (Itv.is_finite size_itv) then UnProven
            else Proven
          in
          let desc =
            "size = " ^ Itv.to_string size_itv ^ ", source = "
            ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | Printf (_, e, loc) | ArrayExp (_, e, loc) | DerefExp (e, loc) ->
      let pid = InterCfg.Node.pid node in
      let taint =
        ItvSem.eval pid e itvmem |> ItvDom.Val.all_locs |> flip Mem.lookup mem
        |> TaintDom.Val.user_input
      in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status = UnProven;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | BufferOverrunLib ("sprintf", [ _; _; e3 ], loc) ->
      let pid = InterCfg.Node.pid node in
      let taint =
        ItvSem.eval pid e3 itvmem |> ItvDom.Val.all_locs |> flip Mem.lookup mem
        |> TaintDom.Val.user_input
      in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status = UnProven;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | BufferOverrunLib ("fread", [ _; _; cnt ], loc) ->
      let pid = InterCfg.Node.pid node in
      let taint = TaintSem.eval pid cnt itvmem mem |> TaintDom.Val.user_input in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status = UnProven;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | _ -> queries

let inspect_aexp_io node aexp itvmem mem queries =
  match aexp with
  | PlusIOExp (e, loc)
  | MinusIOExp (e, loc)
  | MultIOExp (e, loc)
  | ShiftIOExp (e, loc)
  | CastIOExp (e, loc) ->
      let pid = InterCfg.Node.pid node in
      let tv = TaintSem.eval pid e itvmem mem in
      let int_overflow, taint =
        (TaintDom.Val.int_overflow tv, TaintDom.Val.user_input tv)
      in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          let status =
            if int_overflow |> TaintDom.IntOverflow.is_bot |> not then UnProven
            else Proven
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | _ -> queries

let inspect_aexp_dz node aexp itvmem mem queries =
  match aexp with
  | DivExp (e, loc) ->
      let pid = InterCfg.Node.pid node in
      let tv = TaintSem.eval pid e itvmem mem in
      let taint = TaintDom.Val.user_input tv in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status = UnProven;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | _ -> queries

let inspect_aexp_nd node aexp itvmem mem queries =
  match aexp with
  | DerefExp (e, loc) ->
      let pid = InterCfg.Node.pid node in
      let taint = TaintSem.eval pid e itvmem mem |> TaintDom.Val.user_input in
      TaintDom.UserInput.fold
        (fun (src_node, src_loc) queries ->
          let desc =
            "source = " ^ Node.to_string src_node ^ " @ "
            ^ CilHelper.s_location src_loc
          in
          {
            node;
            exp = aexp;
            loc;
            allocsite = None;
            status = UnProven;
            desc;
            src = Some (src_node, src_loc);
          }
          :: queries)
        taint queries
  | _ -> queries

let generate spec (global, mem, target) =
  let nodes = InterCfg.nodes_of global.icfg in
  let total = List.length nodes in
  list_fold
    (fun node (qs, k) ->
      prerr_progressbar ~itv:1000 k total;
      let ptrmem = ItvDom.Table.find node spec.Spec.ptrinfo in
      let mem = Table.find node mem in
      let cmd = InterCfg.cmd_of global.icfg node in
      let aexps = AlarmExp.collect analysis cmd in
      let qs =
        list_fold
          (fun aexp ->
            if mem = Mem.bot then id (* dead code *)
            else
              match target with
              | BO -> inspect_aexp_bo node aexp ptrmem mem
              | IO -> inspect_aexp_io node aexp ptrmem mem
              | DZ -> inspect_aexp_dz node aexp ptrmem mem
              | ND -> inspect_aexp_nd node aexp ptrmem mem)
          aexps qs
      in
      (qs, k + 1))
    nodes ([], 0)
  |> fst

let inspect_alarm global spec inputof =
  (if !Options.bo then generate spec (global, inputof, Report.BO) else [])
  @ (if
     !Options.mult_io || !Options.plus_io || !Options.minus_io
     || !Options.shift_io || !Options.cast_io
    then generate spec (global, inputof, Report.IO)
    else [])
  @ (if !Options.nd then generate spec (global, inputof, Report.ND) else [])
  @ if !Options.dz then generate spec (global, inputof, Report.DZ) else []

let get_locset mem =
  ItvDom.Mem.foldi
    (fun l v locset ->
      locset |> PowLoc.add l
      |> PowLoc.union (ItvDom.Val.pow_loc_of_val v)
      |> BatSet.fold
           (fun a -> PowLoc.add (Loc.of_allocsite a))
           (ItvDom.Val.allocsites_of_val v))
    mem PowLoc.empty

let make_top_mem locset =
  PowLoc.fold (fun l mem -> Mem.add l TaintDom.Val.top mem) locset Mem.bot

let print_datalog_fact _ global dug alarms =
  if !Options.patron then RelDUGraph.print_patron analysis global dug alarms
  else (
    RelSyntax.print analysis global.icfg;
    Provenance.print analysis global.relations;
    RelDUGraph.print analysis global dug alarms;
    RelDUGraph.print_taint_alarm analysis alarms)

let ignore_function node =
  BatSet.elements !Options.filter_function
  |> List.map Str.regexp
  |> List.exists (fun re -> Str.string_match re (InterCfg.Node.pid node) 0)

let post_process spec itvdug (global, _, inputof, outputof) =
  let alarms =
    StepManager.stepf true "Generate Alarm Report"
      (inspect_alarm global spec)
      inputof
    |> List.filter (fun a ->
           match a.src with
           | Some (n, _) ->
               (not (ignore_function a.Report.node)) && not (ignore_function n)
           | None -> not (ignore_function a.Report.node))
  in
  let report_file =
    open_out (FileManager.analysis_dir analysis ^ "/report.txt")
  in
  let fmt = F.formatter_of_out_channel report_file in
  Report.print ~fmt:(Some fmt) global alarms;
  close_out report_file;
  if !Options.extract_datalog_fact_full then
    print_datalog_fact spec global itvdug alarms;
  (global, inputof, outputof, alarms)

let do_analysis (global, itvdug, itvinputof) =
  let global = { global with table = itvinputof } in
  let locset = get_locset global.mem in
  let spec =
    {
      Spec.empty with
      analysis;
      locset;
      locset_fs = locset;
      premem = make_top_mem locset;
      ptrinfo = itvinputof;
    }
  in
  (* NOTE: fully flow-sensitive taint analysis *)
  let _ = Options.pfs := 100 in
  let dug = Analysis.generate_dug spec global in
  (if !Options.marshal_in then marshal_in global
  else Analysis.perform spec global dug)
  |> opt !Options.marshal_out marshal_out
  |> post_process spec itvdug
