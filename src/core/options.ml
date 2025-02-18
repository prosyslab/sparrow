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

type task = All | Capture | Analyze
type frontend = Claml | Cil

let task = ref All
let entry_point = ref "main"
let skip_main_analysis = ref false

(* Capture *)
let skip_build = ref false
let build_commands = ref []
let frontend = ref Cil

(* IL *)
let il = ref false
let cfg = ref false
let dug = ref false
let optil = ref true
let cut_cyclic_call = ref false
let keep_unreachable = ref false
let keep_unreachable_from = ref BatSet.empty

(* Context & Flow Sensitivity *)
let inline = ref []
let inline_size = ref 100000
let pfs = ref 100

let pfs_wv =
  ref
    "100.0 -100.0 -34.988241686898462 -99.662940999334793 -100.0\n\
    \   20.989776538253508 100.0 28.513793013882694 -30.30168857094921 -100.0\n\
    \   27.574102626204336 -74.381386730147895 -65.270452404579814 100.0 100.0\n\
    \   80.703727126015522 -13.475885118852554 -100.0 67.910455368871894 -100.0\n\
    \   -100.0 -58.103715871839746 -100.0 100.0 -2.1779606787169481\n\
    \   50.854271919870321 87.790748577623447 100.0 100.0 -100.0\n\
    \   -100.0 100.0 70.038390871188767 -22.179572133292666 100.0\n\
    \   42.647897970881758 100.0 -100.0 -100.0 32.564292030707847\n\
    \   98.370519929542738 100.0 100.0 -100.0 -100.0"

(* Octagon Analysis *)
let oct = ref false
let pack_impact = ref true
let pack_manual = ref false

(* Taint Analysis *)
let taint = ref false

(* Analyzer *)

let nobar = ref false
let narrow = ref false
let profile = ref false
let scaffold = ref true

(* Transformation *)

let unwrap_alloc = ref false

(* Unsoundness *)
let max_pre_iter = ref 0
let unsound_loop = ref BatSet.empty
let unsound_lib = ref BatSet.empty
let extract_loop_feat = ref false
let extract_lib_feat = ref false
let top_location = ref false
let unsound_recursion = ref false
let unsound_alloc = ref false
let unsound_const_string = ref false
let unsound_skip_file = ref []
let unsound_noreturn_function = ref false
let unsound_skip_function = ref []
let unsound_skip_global_array_init = ref max_int
let bugfinder = ref 0

(* datalog *)
let extract_datalog_fact = ref false
let extract_datalog_fact_full = ref false
let extract_datalog_fact_full_no_opt = ref false

(* for patron *)
let patron = ref false
let target_loc = ref []
let target_alarm_map = ref BatMap.empty

let add_target_alarm s =
  match String.split_on_char '=' s with
  | [ targ_id; targ_point ] ->
      target_alarm_map := BatMap.add targ_id targ_point !target_alarm_map
  | _ ->
      print_endline "Invalid slice option (must be '-target_alarm X=file:line')";
      exit 1

(* remove cast exp for patron *)
let remove_cast = ref false

(* Alarm Report *)
let noalarm = ref false
let bo = ref true
let nd = ref false
let detailed_io = ref false
let plus_io = ref false
let minus_io = ref false
let mult_io = ref false
let shift_io = ref false
let cast_io = ref false
let dz = ref false
let show_all_query = ref false
let filter_extern = ref false
let filter_global = ref false
let filter_lib = ref false
let filter_complex_exp = ref false
let filter_rec = ref false
let filter_allocsite = ref BatSet.empty
let filter_file = ref BatSet.empty
let filter_function = ref BatSet.empty
let filter_node = ref BatSet.empty

(* Input & OUtput *)
let outdir = ref "sparrow-out"
let marshal_in = ref false
let marshal_out = ref false

(* DUG slice *)
let slice_target_map = ref BatMap.empty

let add_slice_target s =
  match String.split_on_char '=' s with
  | [ targ_id; targ_point ] ->
      slice_target_map := BatMap.add targ_id targ_point !slice_target_map
  | _ ->
      print_endline "Invalid slice option (must be '-slice X=file:line')";
      exit 1

let full_slice = ref false
let max_control_deps = ref 0

(* Debug *)
let debug = ref false
let oct_debug = ref false
let taint_debug = ref false

(* ETC *)
let print_pre_mem = ref false
let verbose = ref 1
let int_overflow = ref false
let memtrace = ref false

let unsoundness_opts =
  [
    ( "-max_pre_iter",
      Arg.Set_int max_pre_iter,
      "Maximum number of iterations for pre-analysis" );
    ( "-unsound_loop",
      Arg.String (fun s -> unsound_loop := BatSet.add s !unsound_loop),
      "Unsound loops" );
    ( "-unsound_lib",
      Arg.String (fun s -> unsound_lib := BatSet.add s !unsound_lib),
      "Unsound libs" );
    ("-unsound_recursion", Arg.Set unsound_recursion, "Unsound recursive calls");
    ( "-unsound_alloc",
      Arg.Set unsound_alloc,
      "Unsound memory allocation (never return null)" );
    ( "-unsound_const_string",
      Arg.Set unsound_const_string,
      "Unsoundly ignore constant string allocations" );
    ( "-unsound_noreturn_function",
      Arg.Set unsound_noreturn_function,
      "Unsoundly ignore functions whose attributes conatin \"__noreturn__\"" );
    ( "-unsound_skip_function",
      Arg.String (fun s -> unsound_skip_function := s :: !unsound_skip_function),
      "Unsoundly ignore functions whose names contain the given argument" );
    ( "-unsound_skip_file",
      Arg.String (fun s -> unsound_skip_file := s :: !unsound_skip_file),
      "Unsoundly ignore files whose names contain the given argument" );
    ( "-unsound_skip_global_array_init",
      Arg.Set_int unsound_skip_global_array_init,
      "Unsoundly ignore global array inits larger than the given argument" );
  ]

let datalog_opts =
  [
    ( "-extract_datalog_fact",
      Arg.Set extract_datalog_fact,
      "Extract simple datalog facts (syntax and def-use graph)" );
    ( "-extract_datalog_fact_full",
      Arg.Unit
        (fun () ->
          extract_datalog_fact := true;
          extract_datalog_fact_full := true),
      "Extract extensive datalog facts" );
    ( "-extract_datalog_fact_full_no_opt",
      Arg.Unit
        (fun () ->
          extract_datalog_fact := true;
          extract_datalog_fact_full := true;
          extract_datalog_fact_full_no_opt := true),
      "Extract extensive datalog facts" );
    ("-remove_cast", Arg.Set remove_cast, "Remove cast expression for encoding");
  ]

let opts =
  [
    ( "-frontend",
      Arg.String
        (fun s -> if s = "claml" then frontend := Claml else frontend := Cil),
      "Frontend" );
    ("-il", Arg.Set il, "Show the input program in IL");
    ("-cfg", Arg.Set cfg, "Print Cfg");
    ("-dug", Arg.Set dug, "Print Def-Use graph");
    ( "-slice",
      Arg.String (fun s -> add_slice_target s),
      "Slice w.r.t a given target" );
    ("-full_slice", Arg.Set full_slice, "Perform full (not thin) slicing");
    ( "-max_control_deps",
      Arg.Set_int max_control_deps,
      "Maximum length of control dependencies to slice" );
    ("-skip_build", Arg.Set skip_build, "Skip build");
    ("-skip_main_analysis", Arg.Set skip_main_analysis, "Skip main analysis");
    ("-entry_point", Arg.Set_string entry_point, "Entry point (default: main)");
    ("-noalarm", Arg.Set noalarm, "Do not print alarms");
    ("-verbose", Arg.Set_int verbose, "Verbose level (default: 1)");
    ("-print_pre_mem", Arg.Set print_pre_mem, "Print pre-analysis memory");
    ("-debug", Arg.Set debug, "Print debug information");
    ( "-oct_debug",
      Arg.Set oct_debug,
      "Print debug information for octagon analysis" );
    ( "-taint_debug",
      Arg.Set taint_debug,
      "Print debug information for taint analysis" );
    ("-pack_impact", Arg.Set pack_impact, "Packing by impact pre-analysis");
    ("-pack_manual", Arg.Set pack_manual, "Pacing by manual annotation");
    ("-nd", Arg.Set nd, "Print Null-dereference alarms");
    ("-bo", Arg.Set bo, "Print Buffer-overrun alarms");
    ("-no_bo", Arg.Clear bo, "Do Not Print Buffer-overrun alarms");
    ( "-io",
      Arg.Unit
        (fun () ->
          plus_io := true;
          minus_io := true;
          mult_io := true;
          shift_io := true;
          cast_io := true),
      "Print all Integer-overflow alarms from binop expressions" );
    ("-pio", Arg.Set plus_io, "Print plus Integer-overflow alarms");
    ("-mio", Arg.Set minus_io, "Print minus Integer-overflow alarms");
    ("-tio", Arg.Set mult_io, "Print multiplication Integer-overflow alarms");
    ("-sio", Arg.Set shift_io, "Print shift Integer-overflow alarms");
    ("-cio", Arg.Set cast_io, "Print cast Integer-overflow alarms");
    ("-patron", Arg.Set patron, "Anlyze for Patron");
    ( "-target_loc",
      Arg.String (fun s -> target_loc := s :: !target_loc),
      "Target location for Patron" );
    ( "-target_alarm",
      Arg.String (fun s -> add_target_alarm s),
      "narrow down the optimization results over the taint analysis based on \
       the alarm specified by Patron" );
    ("-dz", Arg.Set dz, "Print Divide-by-zero alarms");
    ( "-bugfinder",
      Arg.Set_int bugfinder,
      "Unsoundness level in bugfinding mode (default: 0)" );
    ( "-inline",
      Arg.String (fun s -> inline := s :: !inline),
      "Inline functions whose names contain X" );
    ( "-inline_size",
      Arg.Set_int inline_size,
      "Size constraint for function inline" );
    ( "-pfs",
      Arg.Set_int pfs,
      "Partial flow-sensitivity -pfs [0-100] (0: flow-insensitive, 100: fully \
       flow-sensitive). default=100" );
    ( "-pfs_wv",
      Arg.String (fun s -> pfs_wv := s),
      "Weight vector for flow-sensitivity (e.g., \"0 1 -1 ... \"). Unspecified \
       weights are zeros." );
    ("-oct", Arg.Set oct, "Do octagon analysis");
    ("-taint", Arg.Set taint, "Do taint analysis");
    ("-profile", Arg.Set profile, "Profiler");
    ("-narrow", Arg.Set narrow, "Do narrowing");
    ( "-extract_loop_feat",
      Arg.Set extract_loop_feat,
      "Extract features of loops for harmless unsoundness" );
    ( "-extract_lib_feat",
      Arg.Set extract_lib_feat,
      "Extract features of libs for harmless unsoundness" );
    ( "-top_location",
      Arg.Set top_location,
      "Treat unknown locations as top locations" );
    ("-scaffold", Arg.Set scaffold, "Use scaffolding semantics (default)");
    ("-no_scaffold", Arg.Clear scaffold, "Do not use scaffolding semantics");
    ("-nobar", Arg.Set nobar, "No progress bar");
    ("-show_all_query", Arg.Set show_all_query, "Show all queries");
    ( "-filter_alarm",
      Arg.Unit
        (fun () ->
          filter_complex_exp := true;
          filter_extern := true;
          filter_global := true;
          filter_lib := true;
          filter_rec := true),
      "Trun on all the filtering options" );
    ( "-filter_allocsite",
      Arg.String (fun s -> filter_allocsite := BatSet.add s !filter_allocsite),
      "Filter alarms from a given allocsite" );
    ( "-filter_file",
      Arg.String (fun s -> filter_file := BatSet.add s !filter_file),
      "Filter alarms from a given file" );
    ( "-filter_function",
      Arg.String (fun s -> filter_function := BatSet.add s !filter_function),
      "Filter alarms from a given file" );
    ( "-filter_node",
      Arg.String (fun s -> filter_node := BatSet.add s !filter_node),
      "Filter alarms from a given file" );
    ( "-filter_complex_exp",
      Arg.Set filter_complex_exp,
      "Filter alarms from complex expressions (e.g., bitwise)" );
    ( "-filter_extern",
      Arg.Set filter_extern,
      "Filter alarms from external allocsites" );
    ( "-filter_global",
      Arg.Set filter_global,
      "Filter alarms from the global area" );
    ( "-filter_lib",
      Arg.Set filter_lib,
      "Filter alarms from library calls (e.g., strcpy)" );
    ( "-filter_rec",
      Arg.Set filter_rec,
      "Filter alarms from recursive call cycles" );
    ("-optil", Arg.Set optil, "Optimize IL (default)");
    ("-no_optil", Arg.Clear optil, "Do not optimize IL");
    ("-cut_cyclic_call", Arg.Set cut_cyclic_call, "Remove cyclic call edges");
    ( "-keep_unreachable",
      Arg.Set keep_unreachable,
      "Keep all unreachable functions" );
    ( "-keep_unreachable_from",
      Arg.String
        (fun s -> keep_unreachable_from := BatSet.add s !keep_unreachable_from),
      "Keep unreachable functions from the given function" );
    ( "-marshal_in",
      Arg.Set marshal_in,
      "Read analysis results from marshaled data" );
    ( "-marshal_out",
      Arg.Set marshal_out,
      "Write analysis results to marshaled data" );
    ("-outdir", Arg.Set_string outdir, "Output directory (default: sparrow-out)");
    ("-int_overflow", Arg.Set int_overflow, "Consider integer overflow");
    ("-memtrace", Arg.Set memtrace, "Profile with memtrace");
    ("-unwrap_alloc", Arg.Set unwrap_alloc, "Unwrap alloc functions");
  ]
  @ unsoundness_opts @ datalog_opts

let capture_opts =
  [
    ("-skip-build", Arg.Set skip_build, "Skip build");
    ( "-frontend",
      Arg.String
        (fun s -> if s = "claml" then frontend := Claml else frontend := Cil),
      "Frontend" );
  ]

let options = ref opts
