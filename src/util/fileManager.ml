module F = Format
module L = Logging

let analysis_dir = function
  | Spec.Pre -> !Options.outdir ^ "/pre"
  | Interval -> !Options.outdir ^ "/interval"
  | OctagonImpact -> !Options.outdir ^ "/octagon-impact"
  | Octagon -> !Options.outdir ^ "/octagon"
  | Taint -> !Options.outdir ^ "/taint"

let mkdir dirname =
  if Sys.file_exists dirname && Sys.is_directory dirname then ()
  else if Sys.file_exists dirname && not (Sys.is_directory dirname) then
    let _ = L.error "Error: %s already exists." dirname in
    exit 1
  else Unix.mkdir dirname 0o755

let mk_outdir () =
  let sub_dirs = [analysis_dir Spec.Interval] in
  let sub_dirs =
    if !Options.taint then sub_dirs @ [analysis_dir Spec.Taint] else sub_dirs
  in
  let sub_dirs =
    if !Options.extract_datalog_fact then
      sub_dirs @ List.map (fun x -> x ^ "/datalog") sub_dirs
    else sub_dirs
  in
  List.iter mkdir (!Options.outdir :: sub_dirs)
