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

let line = String.make 80 '-'

let step s stg i fn =
  let t0 = Sys.time () in
  let to_consol = true in
  if s then
    Logging.info ~to_consol "\n\n\n%s\n%s begins...\n%s\n" line stg line
  else Logging.info ~to_consol "%s begins...\n" stg ;
  let v = fn i in
  if s then Logging.info ~to_consol "\n" ;
  Logging.info ~to_consol "%s completes: %f\n" stg (Sys.time () -. t0) ;
  v

let stepf s stg fn i = if !Options.verbose >= 1 then step s stg i fn else fn i

let stepf_opt b s stg fn i =
  if b && !Options.verbose >= 1 then step s stg i fn else if b then fn i else i

let stepf_cond b s stg fn1 fn2 i =
  if b && !Options.verbose >= 1 then step s stg i fn1
  else if (not b) && !Options.verbose >= 1 then step s stg i fn2
  else if b then fn1 i
  else fn2 i

let stepf_switch s stg fn_list i =
  let fn = List.find fst fn_list |> snd in
  if !Options.verbose >= 1 then step s stg i fn else fn i

let stepf_opt_unit b s stg fn i = if b then step s stg i fn else ()
