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

open Global
open Vocab
module L = Logging

(* transformation based on syntactic heuristics *)
let transform_simple file =
  opt !Options.unsound_alloc UnsoundAlloc.transform file

(* transformation based on semantic heuristics *)
let transform global =
  let loop_transformed = UnsoundLoop.transform global in
  let inlined = Frontend.inline global in
  if (not !Options.il) && (loop_transformed || inlined) then
    (* NOTE: CFG must be re-computed after transformation *)
    Frontend.makeCFGinfo global.file
    |> StepManager.stepf true "Translation to graphs (after inline)" Global.init
    |> StepManager.stepf true "Pre-analysis (after inline)" PreAnalysis.perform
  else (* nothing changed *)
    global

let marshal_in file =
  let filename = Filename.basename file.Cil.fileName in
  MarshalManager.input (filename ^ ".global")

let marshal_out file global =
  let filename = Filename.basename file.Cil.fileName in
  MarshalManager.output (filename ^ ".global") global;
  global

let init_analysis file =
  if !Options.marshal_in then marshal_in file
  else
    file |> transform_simple
    |> StepManager.stepf true "Translation to graphs" Global.init
    |> StepManager.stepf true "Pre-analysis" PreAnalysis.perform
    |> transform
    |> opt !Options.marshal_out (marshal_out file)

let print_pgm_info global =
  let pids = InterCfg.pidsof global.icfg in
  let nodes = InterCfg.nodesof global.icfg in
  L.info "#Procs : %d\n" (List.length pids);
  L.info "#Nodes : %d\n" (List.length nodes);
  let oc = open_out (!Options.outdir ^ "/node.json") in
  let json = InterCfg.to_json_simple global.icfg in
  Yojson.Safe.pretty_to_channel oc json;
  close_out oc;
  global

let print_il file =
  (if !Options.inline = [] && BatSet.is_empty !Options.unsound_loop then
   Cil.dumpFile !Cil.printerForMaincil stdout "" (transform_simple file)
  else
    let global = init_analysis file in
    Cil.dumpFile !Cil.printerForMaincil stdout "" global.file);
  exit 0

let print_cfg global =
  let oc = open_out (Filename.concat !Options.outdir "cfg.json") in
  `Assoc
    [
      ("callgraph", CallGraph.to_json global.callgraph);
      ("cfgs", InterCfg.to_json global.icfg);
    ]
  |> Yojson.Safe.pretty_to_channel oc;
  close_out oc;
  global

let finalize t0 =
  L.info ~level:1 "Finished properly.\n";
  Profiler.report stdout;
  L.info ~level:1 "%f\n" (Sys.time () -. t0);
  L.finalize ()

let octagon_analysis (global, _, itvinputof, _, _) =
  StepManager.stepf true "Oct Sparse Analysis" OctAnalysis.do_analysis
    (global, itvinputof)
  |> fun (global, _, _, alarms) -> (global, alarms)

let taint_analysis (global, itvdug, itvinputof, _, itvalarms) =
  StepManager.stepf true "Taint Sparse Analysis" TaintAnalysis.do_analysis
    (global, itvdug, itvinputof)
  |> fun (global, _, _, alarms) -> (global, itvalarms @ alarms)

let extract_feature global =
  if !Options.extract_loop_feat then
    let _ = UnsoundLoop.extract_feature global |> UnsoundLoop.print_feature in
    exit 0
  else if !Options.extract_lib_feat then
    let _ = UnsoundLib.extract_feature global |> UnsoundLib.print_feature in
    exit 0
  else global

let initialize () =
  Printexc.record_backtrace true;
  (* process arguments *)
  let usageMsg = "Usage: sparrow [options] source-files" in
  Arg.parse_dynamic Options.options Frontend.parse_arg usageMsg;
  FileManager.mk_outdir ();
  L.init ();
  if !Options.debug then L.set_level L.DEBUG;
  L.info "%s\n" (String.concat " " !Frontend.files);
  Profiler.start_logger ();
  Cil.initCIL ();
  if !Options.memtrace then
    Memtrace.start_tracing ~context:(Some "sparrow") ~sampling_rate:1e-6
      ~filename:(Filename.concat !Options.outdir "memtrace")
    |> ignore

let main () =
  let t0 = Sys.time () in
  initialize ();
  match !Options.task with
  | Options.Capture -> Capture.run ()
  | _ ->
      ( StepManager.stepf true "Front-end" Frontend.parse ()
      |> Frontend.makeCFGinfo |> opt !Options.il print_il |> init_analysis
      |> print_pgm_info |> opt !Options.cfg print_cfg |> extract_feature
      |> StepManager.stepf true "Itv Sparse Analysis" ItvAnalysis.do_analysis
      |> case
           [
             (!Options.oct, octagon_analysis); (!Options.taint, taint_analysis);
           ]
           (fun (global, _, _, _, alarm) -> (global, alarm))
      |> fun (global, alarm) -> Report.print global alarm )
      |> fun () -> finalize t0

let _ = main ()
