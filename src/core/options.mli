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
(** Commandline options *)

type task = All | Capture | Analyze
type frontend = Claml | Cil

val task : task ref
val skip_build : bool ref
val build_commands : string list ref
val frontend : frontend ref

(** {2 Intermediate Represenation } *)

val il : bool ref
val cfg : bool ref
val dug : bool ref
val optil : bool ref
val cut_cyclic_call : bool ref
val keep_unreachable : bool ref
val keep_unreachable_from : string BatSet.t ref

(** {2 Context Sensitivity } *)

val inline : string list ref
val inline_size : int ref
val pfs : int ref
val pfs_wv : string ref

(** {2 Octagon Analysis } *)

val oct : bool ref
val pack_impact : bool ref
val pack_manual : bool ref

(** {2 Taint Analysis } *)

val taint : bool ref

(** {2 Unsoundness } *)

val max_pre_iter : int ref
val unsound_loop : string BatSet.t ref
val unsound_lib : string BatSet.t ref
val extract_loop_feat : bool ref
val extract_lib_feat : bool ref
val top_location : bool ref
val bugfinder : int ref
val unsound_recursion : bool ref
val unsound_alloc : bool ref
val unsound_const_string : bool ref
val unsound_noreturn_function : bool ref
val unsound_skip_function : string list ref
val unsound_skip_file : string list ref
val unsound_skip_global_array_init : int ref

(** {2 Main Analysis } *)

val entry_point : string ref
val skip_main_analysis : bool ref
val narrow : bool ref
val scaffold : bool ref
val int_overflow : bool ref
val memtrace : bool ref

(* Transformation *)

val unwrap_alloc : bool ref

(** {2 Alarm Report } *)

val bo : bool ref
val nd : bool ref
val detailed_io : bool ref
val plus_io : bool ref
val minus_io : bool ref
val mult_io : bool ref
val shift_io : bool ref
val cast_io : bool ref
val dz : bool ref
val show_all_query : bool ref
val filter_extern : bool ref
val filter_global : bool ref
val filter_lib : bool ref
val filter_complex_exp : bool ref
val filter_rec : bool ref
val filter_allocsite : string BatSet.t ref
val filter_file : string BatSet.t ref
val filter_function : string BatSet.t ref
val filter_node : string BatSet.t ref
val extract_datalog_fact : bool ref
val extract_datalog_fact_full : bool ref
val extract_datalog_fact_full_no_opt : bool ref
val remove_cast : bool ref
val patron : bool ref
val target_loc : string list ref
val target_alarm_map : (string, string) BatMap.t ref

(** {2 Pretty Printer & Debugging } *)

val nobar : bool ref
val profile : bool ref
val noalarm : bool ref
val debug : bool ref
val oct_debug : bool ref
val print_pre_mem : bool ref
val verbose : int ref

(** {2 Input & Output } *)

val outdir : string ref
val marshal_in : bool ref
val marshal_out : bool ref

(** {3 DUG slice } *)

val slice_target_map : (string, string) BatMap.t ref
val full_slice : bool ref
val max_control_deps : int ref

(** {2 Options lists } *)

val options : (string * Arg.spec * string) list ref
val opts : (string * Arg.spec * string) list
val capture_opts : (string * Arg.spec * string) list
