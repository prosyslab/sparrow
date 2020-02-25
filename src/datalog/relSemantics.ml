open BasicDom
module F = Format

module Alloc = struct
  (* Alloc(n, lv, e, l): l points to an abstract location allocated at n *)
  type t = Node.t * CilHelper.Lval.t * CilHelper.Exp.t * Loc.t
  [@@deriving compare]

  let make n lv e l = (n, lv, e, l)
end

module Assign = struct
  type t = Loc.t * Loc.t * Loc.t [@@deriving compare]

  let make x y z = (x, y, z)
end

module LocPair = struct
  type t = Loc.t * Loc.t [@@deriving compare]

  let pp fmt (x, y) = F.fprintf fmt "PointsTo(%a, %a)" Loc.pp x Loc.pp y
end

module LocPairSet = struct
  include Set.Make (LocPair)

  let pp fmt set =
    let x = elements set in
    F.pp_print_list ~pp_sep:(fun fmt () -> F.fprintf fmt ", ") LocPair.pp fmt x

  let pp_premise fmt set =
    let x = elements set in
    F.fprintf fmt "NOT ";
    F.pp_print_list
      ~pp_sep:(fun fmt () -> F.fprintf fmt ", NOT ")
      LocPair.pp fmt x
end

module AssignSet = struct
  type t = Node.t * CilHelper.Lval.t * CilHelper.Exp.t * LocPairSet.t
  [@@deriving compare]

  let make n l e set = (n, l, e, set)
end

module PointsTo = struct
  type t = Loc.t * Loc.t * provenance

  and provenance =
    | Alloc of Alloc.t
    | Assign of Assign.t
    | AssignSet of AssignSet.t
  [@@deriving compare]

  let make_alloc n lv e l r = (l, r, Alloc (Alloc.make n lv e l))

  (* PointsTo(x, z) :- Assign(x,y), PointsTo(y,z) *)
  let make_assign x y z = (x, z, Assign (Assign.make x y z))

  let make_assign_set n l e x y set =
    (x, y, AssignSet (AssignSet.make n l e set))

  let pp fmt (l, r, p) =
    match p with
    | Alloc (n, lv, e, _) ->
        let lv_id = Hashtbl.find RelSyntax.lv_map lv in
        let exp_id = Hashtbl.find RelSyntax.exp_map e in
        F.fprintf fmt "R0: NOT Alloc(%a,%s,%s), PointsTo(%a,%a)" Node.pp n lv_id
          exp_id Loc.pp l Loc.pp r
    | Assign (x, y, z) ->
        F.fprintf fmt
          "R1: NOT Assign(%a,%a), NOT PointsTo(%a,%a), points_to(%a, %a)" Loc.pp
          x Loc.pp y Loc.pp y Loc.pp z Loc.pp l Loc.pp r
    | AssignSet (n, lv, e, set) ->
        let lv_id = Hashtbl.find RelSyntax.lv_map lv in
        let exp_id = Hashtbl.find RelSyntax.exp_map e in
        F.fprintf fmt "R2: NOT Assign(%a,%s,%s), %a, PointsTo(%a,%a)" Node.pp n
          lv_id exp_id LocPairSet.pp_premise set Loc.pp l Loc.pp r
end

module Bind = struct
  type t = Loc.t * Loc.t [@@deriving compare]

  let make x y = (x, y)

  let pp fmt (x, y) = F.fprintf fmt "Bind: Bind(%a,%a)" Loc.pp x Loc.pp y
end

module Relation = struct
  type t = PointsTo of PointsTo.t | Bind of Bind.t [@@deriving compare]

  let points_to x = PointsTo x

  let bind x = Bind x

  let pp fmt = function
    | PointsTo r -> PointsTo.pp fmt r
    | Bind r -> Bind.pp fmt r
end

module Set = struct
  include Set.Make (Relation)

  let pp fmt set = iter (fun r -> F.fprintf fmt "%a\n" Relation.pp r)
end

include Relation
