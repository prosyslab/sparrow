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
type analysis = Pre | Interval | OctagonImpact | Octagon | Taint
module type S =
sig
  module Dom : InstrumentedMem.S

  type t = {
    analysis : analysis;
    locset : Dom.PowA.t;
    locset_fs : Dom.PowA.t;
    ptrinfo : ItvDom.Table.t;
    premem : Dom.t;
    (* unsoundness *)
    unsound_lib : string BatSet.t;
    unsound_update : bool;
    unsound_bitwise : bool;
  }
  val empty : t
  val is_interval : t -> bool
end

module Make(Dom: InstrumentedMem.S) =
struct
  module Dom = Dom
  module PowLoc = Dom.PowA

  type t = {
    analysis : analysis;
    locset : PowLoc.t;
    locset_fs : PowLoc.t;
    ptrinfo : ItvDom.Table.t;
    premem : Dom.t;
    (* unsoundness *)
    unsound_lib : string BatSet.t;
    unsound_update : bool;
    unsound_bitwise : bool;
  }

  let empty = {
    analysis = Pre;
    locset = Dom.PowA.bot;
    locset_fs = Dom.PowA.bot;
    ptrinfo = ItvDom.Table.empty;
    premem = Dom.bot;
    unsound_lib = BatSet.empty;
    unsound_update = false;
    unsound_bitwise = false;
  }

  let is_interval spec = (spec.analysis = Interval)
end
