open BasicDom
open Vocab
module F = Format
module G = Graph.Persistent.Digraph.ConcreteBidirectional (Loc)
module Rel = RelSemantics

let add_alloc n lv e l r relations =
  let rel = Rel.PointsTo.make_alloc n lv e l r |> Rel.points_to in
  Rel.Set.add rel relations

let alloc analysis n lv e ploc v relations =
  if analysis = Spec.Pre then
    let rvset = ItvDom.Val.all_locs v in
    PowLoc.fold
      (fun l -> PowLoc.fold (fun r -> add_alloc n lv e l r) rvset)
      ploc relations
  else relations

let rec extract prov l set =
  match G.pred prov l with
  | [] -> set
  | lst -> List.fold_left (fun set p -> Rel.LocPairSet.add (p, l) set) set lst
  | exception _ -> set

let add_set icfg node l r prov relations =
  match InterCfg.cmdof icfg node with
  | IntraCfg.Cmd.Cset (lv, e, _) ->
      let pairset = extract prov r Rel.LocPairSet.empty in
      let rel =
        Rel.PointsTo.make_assign_set node lv e l r pairset |> Rel.points_to
      in
      Rel.Set.add rel relations
  | _ -> relations

let set analysis icfg node e ploc v prov relations =
  if
    analysis = Spec.Pre
    && (Cil.isPointerType @@ Cil.unrollTypeDeep @@ Cil.typeOf e)
  then
    let rvset = ItvDom.Val.all_locs v |> PowLoc.remove Loc.null in
    PowLoc.fold
      (fun l relations ->
        PowLoc.fold
          (fun r relations -> add_set icfg node l r prov relations)
          rvset relations)
      ploc relations
  else relations

let all_locs prov =
  G.fold_vertex (fun v l -> if Loc.equal v Loc.dummy then l else v :: l) prov []

let call analysis icfg node arg_lvars_set prov_list relations =
  if analysis = Spec.Pre then
    let is_same_length l = List.length l = List.length prov_list in
    let arg_lvars_set = BatSet.filter is_same_length arg_lvars_set in
    BatSet.fold
      (fun arg_lvars relations ->
        List.fold_left2
          (fun relations formal prov ->
            let locs = all_locs prov in
            List.fold_left
              (fun relations l ->
                let rel = Rel.Bind.make l formal in
                Rel.bind rel |> flip Rel.Set.add relations)
              relations locs)
          relations arg_lvars prov_list)
      arg_lvars_set relations
  else relations

let print analysis relations =
  let dirname = FileManager.analysis_dir analysis ^ "/datalog/" in
  let oc_prov = open_out (dirname ^ "/provenence.txt") in
  let oc_ptr = open_out (dirname ^ "/PointsTo.facts") in
  let oc_bind = open_out (dirname ^ "/Bind.facts") in
  let fmt_prov = Format.formatter_of_out_channel oc_prov in
  let fmt_ptr = Format.formatter_of_out_channel oc_ptr in
  let fmt_bind = Format.formatter_of_out_channel oc_bind in
  Rel.Set.pp fmt_prov "%s\n" relations;
  Rel.Set.iter
    (function
      | Rel.PointsTo (x, y, _) -> F.fprintf fmt_ptr "%a\t%a\n" Loc.pp x Loc.pp y
      | Rel.Bind (x, y) -> F.fprintf fmt_bind "%a\t%a\n" Loc.pp x Loc.pp y)
    relations;
  close_out oc_prov;
  close_out oc_bind;
  close_out oc_ptr
