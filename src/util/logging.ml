module F = Format

type formatter = {file: F.formatter; dual: F.formatter}

type level = DEBUG | INFO | WARN | ERROR

let logger = ref None

let reporter = ref None

let level = ref INFO

let log_file = ref None

let report_file = ref None

let copy_formatter f =
  let out_string, flush = F.pp_get_formatter_output_functions f () in
  let out_funs = F.pp_get_formatter_out_functions f () in
  let new_f = F.make_formatter out_string flush in
  F.pp_set_formatter_out_functions new_f out_funs ;
  new_f

let dual_formatter fmt1 fmt2 =
  let out_fun1 = F.pp_get_formatter_out_functions fmt1 () in
  let out_fun2 = F.pp_get_formatter_out_functions fmt2 () in
  let fmt = copy_formatter fmt1 in
  F.pp_set_formatter_out_functions fmt
    { F.out_string=
        (fun s p n -> out_fun1.out_string s p n ; out_fun2.out_string s p n)
    ; out_indent= (fun n -> out_fun1.out_indent n ; out_fun2.out_indent n)
    ; out_flush= (fun () -> out_fun1.out_flush () ; out_fun2.out_flush ())
    ; out_newline= (fun () -> out_fun1.out_newline () ; out_fun2.out_newline ())
    ; out_spaces= (fun n -> out_fun1.out_spaces n ; out_fun2.out_spaces n) } ;
  fmt

let init level =
  let log_oc = open_out (!Options.outdir ^ "/log.txt") in
  let report_oc = open_out (!Options.outdir ^ "/report.txt") in
  let log_file_fmt = F.formatter_of_out_channel log_oc in
  let log_dual_fmt = dual_formatter log_file_fmt F.err_formatter in
  let report_file_fmt = F.formatter_of_out_channel report_oc in
  let report_dual_fmt = dual_formatter report_file_fmt F.err_formatter in
  log_file := Some log_oc ;
  report_file := Some report_oc ;
  logger := Some {file= log_file_fmt; dual= log_dual_fmt} ;
  reporter := Some {file= report_file_fmt; dual= report_dual_fmt}

let close_channel = function Some oc -> close_out oc | None -> ()

let flush = function
  | Some logger ->
      F.pp_print_flush logger.file () ;
      F.pp_print_flush logger.dual ()
  | _ -> ()

let finalize () =
  flush !logger ;
  flush !reporter ;
  close_channel !log_file ;
  close_channel !report_file

let compare_level set_level level =
  match (set_level, level) with
  | DEBUG, _
   |INFO, INFO
   |INFO, WARN
   |INFO, ERROR
   |WARN, WARN
   |WARN, ERROR
   |ERROR, ERROR ->
      true
  | _, _ -> false

let log to_consol logger lv =
  match logger with
  | Some logger when compare_level !level lv ->
      if to_consol then F.fprintf logger.dual else F.fprintf logger.file
  | _ -> F.ifprintf F.err_formatter

let debug ?(to_consol = false) = log to_consol !logger DEBUG

let info ?(to_consol = true) ?(level = 0) =
  if level <= !Options.verbose then log to_consol !logger INFO
  else F.ifprintf F.err_formatter

let warn ?(to_consol = true) = log to_consol !logger WARN

let error ?(to_consol = true) = log to_consol !logger ERROR

let report ?(to_consol = false) = log to_consol !reporter INFO
