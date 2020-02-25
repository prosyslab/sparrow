module L = Logging

let json_to_string = function `String s -> s | _ -> failwith "Invalid json"

let json_to_list = function `List l -> l | _ -> failwith "Invalid json"

let json_to_assoc = function `Assoc a -> a | _ -> failwith "Invalid json"

let rec create_dirs path =
  if Sys.file_exists path then ()
  else (
    prerr_endline path;
    Filename.dirname path |> create_dirs;
    FileManager.mkdir path )

let preprocess_one_file cwd entry =
  let directory = List.assoc "directory" entry |> json_to_string in
  let outdir = Filename.concat !Options.outdir "preprocess" in
  let outdir = Filename.concat cwd outdir in
  let outdir = Str.replace_first (Str.regexp cwd) outdir directory in
  let file = List.assoc "file" entry |> json_to_string in
  let outfile = Filename.concat outdir file in
  (* file may contain directories *)
  Filename.dirname outfile |> create_dirs;
  let args =
    List.assoc "arguments" entry
    |> json_to_list
    |> List.fold_left
         (fun l arg ->
           match json_to_string arg with
           | "-c" -> l @ [ "-E" ]
           | f when Filename.extension f = ".c" ->
               l @ [ file ] (* replace with absolute path *)
           | f when Filename.extension f = ".o" ->
               l @ [ outfile ^ ".i" ] (* replace with .i *)
           | f -> l @ [ f ])
         []
  in
  Unix.chdir directory;
  let _ =
    Unix.create_process "cc" (args |> Array.of_list) Unix.stdin Unix.stdout
      Unix.stderr
  in
  ()

let preprocess () =
  let cwd = Sys.getcwd () in
  Yojson.Safe.from_file "compile_commands.json"
  |> json_to_list
  |> List.fold_left
       (fun () entry ->
         let entry = json_to_assoc entry in
         preprocess_one_file cwd entry)
       ();
  Unix.chdir cwd

let run_bear () =
  let commands = "bear" :: !Options.build_commands in
  let _ =
    Unix.create_process "bear" (Array.of_list commands) Unix.stdin Unix.stdout
      Unix.stderr
  in
  match Unix.wait () with
  | _, Unix.WEXITED _ -> ()
  | _, _ ->
      L.error "Invalid build command";
      exit 1

let run () =
  if not !Options.skip_build then run_bear ();
  preprocess ()
