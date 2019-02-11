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

let output name data =
  let dirname = !Options.outdir ^ "/marshal" in
  if not (Sys.file_exists dirname) then Unix.mkdir dirname 0o755 ;
  let chan = open_out (dirname ^ "/" ^ name) in
  Marshal.to_channel chan data [] ;
  close_out chan

let input name =
  let dirname = !Options.outdir ^ "/marshal" in
  if not (Sys.file_exists dirname) then failwith (dirname ^ " not found") ;
  let chan = open_in (dirname ^ "/" ^ name) in
  let data = Marshal.from_channel chan in
  close_in chan ; data
