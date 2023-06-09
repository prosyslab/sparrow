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

module type S = sig
  include AbsSem.S

  module Access :
    Access.S with type t = Dom.Access.t and type Info.t = Dom.Access.Info.t

  val accessof :
    ?locset:Dom.PowA.t ->
    Global.t ->
    BasicDom.Node.t ->
    (BasicDom.Node.t -> Dom.t * Global.t -> Dom.t * Global.t) ->
    Dom.t ->
    Access.info
end

module Make (Sem : AbsSem.S) = struct
  include Sem
  module Access = Sem.Dom.Access

  let accessof ?locset:(_ = Dom.PowA.empty) global node f mem =
    Dom.init_access ();
    let _ = f node (mem, global) in
    Dom.return_access ()
end

module SlicingSem = struct
  include ItvSem
  module Access = ItvSem.Dom.Access

  let accessof ?locset:(_ = ItvSem.Dom.PowA.empty) global node _ mem =
    let du_info = DefUse.eval_def_use global mem node in
    let targets = SlicingUtils.get_target_nodes () in
    let uses =
      if InterCfg.NodeSet.mem node targets then
        DefUse.eval_use_of_targ global mem node
      else du_info.uses
    in
    Access.Info.add_set Access.Info.def du_info.defs Access.Info.empty
    |> Access.Info.add_set Access.Info.use uses
end