open ProsysCil
open Cil
open Vocab
open ApiSem
module Node = InterCfg.Node
module Proc = InterCfg.Proc
module PowLoc = BasicDom.PowLoc
module PowProc = BasicDom.PowProc
module Loc = BasicDom.Loc
module Val = ItvDom.Val
module DefUseMap = BatMap.Make (Loc)

let target_nodes = ref InterCfg.NodeSet.empty

let register_target global targ_str =
  let targ_node_set = InterCfg.nodes_of_line global.Global.icfg targ_str in
  target_nodes := InterCfg.NodeSet.union targ_node_set !target_nodes

let get_target_nodes () = !target_nodes

module DefUseInfo = struct
  type t = { du_map : PowLoc.t DefUseMap.t; defs : PowLoc.t; uses : PowLoc.t }

  let make du_map =
    let f k v (defs, uses) = (PowLoc.add k defs, PowLoc.union v uses) in
    let defs, uses = DefUseMap.fold f du_map (PowLoc.empty, PowLoc.empty) in
    { du_map; defs; uses }

  let lookup_def loc du_info = DefUseMap.find loc du_info.du_map

  let lookup_defs locs du_info =
    let folder l acc = PowLoc.union (lookup_def l du_info) acc in
    PowLoc.fold folder locs PowLoc.empty
end

type api_uses = {
  src : PowLoc.t;
  dst : PowLoc.t;
  buf : PowLoc.t;
  size : PowLoc.t;
}

let empty_uses =
  {
    src = PowLoc.empty;
    dst = PowLoc.empty;
    buf = PowLoc.empty;
    size = PowLoc.empty;
  }

let rec strong_updatable = function
  | Loc.GVar _ -> true
  | Loc.LVar _ -> true (* For slicing, don't need to consider recursion *)
  | Loc.Allocsite _ -> false
  | Loc.Field (l, _, _) -> strong_updatable l

let add_assign lv_locs uses map =
  let strong_update =
    PowLoc.cardinal lv_locs <= 1 && PowLoc.for_all strong_updatable lv_locs
  in
  let folder def acc =
    if strong_update then DefUseMap.add def uses acc
    else DefUseMap.add def (PowLoc.add def uses) acc
  in
  PowLoc.fold folder lv_locs map

(* Update def-use map to reflect a sequence of assignments on arguments *)
let rec add_arg_assigns arg_list uses_list map =
  match (arg_list, uses_list) with
  | [], _ | _, [] -> map (* There can be variable arguments *)
  | head_arg :: tail_args, head_uses :: tail_uses_list ->
      let arg_defs = PowLoc.singleton head_arg in
      let map = add_assign arg_defs head_uses map in
      add_arg_assigns tail_args tail_uses_list map

let rec use_of_exp pid e mem is_full =
  match e with
  | Cil.Const _ -> PowLoc.empty
  | Cil.Lval lv | Cil.StartOf lv ->
      (* Union (1) locs that are used to resolve where 'lv' points to, and (2)
       * locs that are actually referred to by 'lv'. Recall that the semantics
       * of this expression is "lookup (eval_lv pid lv mem) mem". Also, note
       * that (1) is decide differently depending on thin/full mode. *)
      PowLoc.union (use_of_lv pid lv mem is_full) (ItvSem.eval_lv pid lv mem)
  | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ -> PowLoc.empty
  | Cil.AlignOf _ | Cil.AlignOfE _ -> PowLoc.empty
  | Cil.UnOp (_, e', _) -> use_of_exp pid e' mem is_full
  | Cil.BinOp (_, e1, e2, _) ->
      let u1 = use_of_exp pid e1 mem is_full in
      let u2 = use_of_exp pid e2 mem is_full in
      PowLoc.union u1 u2
  | Cil.Question (e1, e2, e3, _) ->
      let u1 = use_of_exp pid e1 mem is_full in
      let u2 = use_of_exp pid e2 mem is_full in
      let u3 = use_of_exp pid e3 mem is_full in
      PowLoc.union u1 (PowLoc.union u2 u3)
  | Cil.CastE (_, e') -> use_of_exp pid e' mem is_full
  | Cil.AddrOf lv -> use_of_lv pid lv mem is_full
  | Cil.AddrOfLabel _ -> invalid_arg "defUse.ml: use_of_exp"

(* Return abslocs used to resolve where 'lv' points to *)
and use_of_lv pid lv mem is_full =
  if not is_full then thin_use_of_offset pid (snd lv) mem
  else
    let base_uses =
      match fst lv with
      (* E.g., we directly know where "x" points to *)
      | Cil.Var _ -> PowLoc.empty
      (* E.g., we should evaluate "p" to know where "*p" points to *)
      | Cil.Mem e -> use_of_exp pid e mem true
    in
    let base_v =
      match fst lv with
      | Cil.Var x ->
          ItvSem.var_of_varinfo x pid |> PowLoc.singleton |> Val.of_pow_loc
      | Cil.Mem e -> ItvSem.eval pid e mem
    in
    let offset_uses = full_use_of_offset pid base_v (snd lv) mem in
    PowLoc.union base_uses offset_uses

and thin_use_of_offset pid os mem =
  match os with
  | Cil.NoOffset -> PowLoc.empty
  | Cil.Field (_, os') -> thin_use_of_offset pid os' mem
  | Cil.Index (e, os') ->
      let idx_loc = use_of_exp pid e mem false in
      PowLoc.union idx_loc (thin_use_of_offset pid os' mem)

(* Return abslocs used to resolve offsets (cf. itvSem.ml:resolve_offset()) *)
and full_use_of_offset pid base_v os mem =
  match os with
  (* e.g., "x = 0;" *)
  | Cil.NoOffset -> PowLoc.empty
  (* e.g., "s.x = 0;" *)
  | Cil.Field (f, os') ->
      let ploc = Val.pow_loc_of_val base_v in
      let arr = Val.array_of_val base_v in
      let str = Val.struct_of_val base_v in
      (* Note that we do not consider 'ploc' here as used, because struct
       * allocations are syntactic features introduced by CIL. *)
      let base_v =
        ItvDom.Mem.lookup ploc mem |> Val.struct_of_val
        |> flip StructBlk.append_field f
        (* S s; p = &s; p->f *)
        |> PowLoc.join (ArrayBlk.append_field arr f)
        (* p = (struct S* )malloc(sizeof(struct S)); p->f *)
        |> PowLoc.join (StructBlk.append_field str f)
        (* S s; s.f *)
        |> Val.of_pow_loc
      in
      full_use_of_offset pid base_v os' mem
  (* e.g., "p[i] = 0;", which is equivalent to "*(p+i) = 0;" *)
  | Cil.Index (e, os') ->
      let base_loc = Val.pow_loc_of_val base_v in
      let idx_loc = use_of_exp pid e mem true in
      let arr = ItvDom.Mem.lookup base_loc mem |> Val.array_of_val in
      let base_v = ArrayBlk.pow_loc_of_array arr |> Val.of_pow_loc in
      PowLoc.union base_loc idx_loc
      |> PowLoc.union (full_use_of_offset pid base_v os' mem)

(* Return the set of abslocs used by 'Src', 'Size', 'Dst', 'Buf' type args *)
let rec collect_uses pid mem is_full arg_typs arg_exps api_uses =
  match (arg_typs, arg_exps) with
  | [], _ | _, [] -> api_uses (* There can be variable arguments *)
  | Src (_, src_typ) :: tail_typs, exp :: tail_exps ->
      let exp =
        if src_typ = Array then Cil.Lval (Cil.Mem exp, Cil.NoOffset) else exp
      in
      let arg_uses = use_of_exp pid exp mem is_full in
      let src_uses = PowLoc.union arg_uses api_uses.src in
      let api_uses = { api_uses with src = src_uses } in
      collect_uses pid mem is_full tail_typs tail_exps api_uses
  | Dst _ :: tail_typs, exp :: tail_exps ->
      let arg_uses = use_of_exp pid exp mem is_full in
      let dst_uses = PowLoc.union arg_uses api_uses.dst in
      let api_uses = { api_uses with dst = dst_uses } in
      collect_uses pid mem is_full tail_typs tail_exps api_uses
  | Buf _ :: tail_typs, exp :: tail_exps ->
      let arg_uses = use_of_exp pid exp mem is_full in
      let buf_uses = PowLoc.union arg_uses api_uses.buf in
      let api_uses = { api_uses with buf = buf_uses } in
      collect_uses pid mem is_full tail_typs tail_exps api_uses
  | Size :: tail_typs, exp :: tail_exps ->
      let arg_uses = use_of_exp pid exp mem is_full in
      let size_uses = PowLoc.union arg_uses api_uses.size in
      let api_uses = { api_uses with size = size_uses } in
      collect_uses pid mem is_full tail_typs tail_exps api_uses
  | _ :: tail_typs, _ :: tail_exps ->
      collect_uses pid mem is_full tail_typs tail_exps api_uses

(* Update def-use map to reflect the definition of return value on 'lv_locs' *)
let process_ret_def lv_locs lv_uses ret_typ api_uses du_map =
  let uses =
    match ret_typ with
    | Const | TaintInput -> lv_uses
    | SrcArg | TopWithSrcTaint -> PowLoc.union lv_uses api_uses.src
    | SizeArg -> PowLoc.union lv_uses api_uses.size
    | DstArg -> PowLoc.union lv_uses api_uses.dst
    | BufArg -> PowLoc.union lv_uses api_uses.buf
    | AllocConst | AllocBuf | AllocStruct | AllocDst -> lv_uses
  in
  add_assign lv_locs uses du_map

(* Update def-use map to reflect the definition on 'AllocDst' return value. *)
let process_alloc_ret node ret_typ api_uses du_map =
  if ret_typ = AllocDst then
    let new_loc =
      BasicDom.Allocsite.allocsite_of_node node |> Loc.of_allocsite
    in
    add_assign (PowLoc.singleton new_loc) api_uses.src du_map
  else du_map

(* Update def-use map to reflect the definition on the arguments *)
let rec process_arg_def node pid mem is_full arg_typs arg_exps api_uses du_map =
  match (arg_typs, arg_exps) with
  | [], _ | _, [] -> du_map (* There can be variable arguments *)
  | Dst (_, is_alloc) :: tail_typs, exp :: tail_exps ->
      let dst_defs = ItvSem.eval_lv pid (Cil.Mem exp, Cil.NoOffset) mem in
      let dst_uses = use_of_lv pid (Cil.Mem exp, Cil.NoOffset) mem is_full in
      let du_map =
        if is_alloc then
          let new_loc =
            BasicDom.Allocsite.allocsite_of_node node |> Loc.of_allocsite
          in
          add_assign (PowLoc.singleton new_loc) api_uses.src du_map
          |> add_assign dst_defs dst_uses
        else add_assign dst_defs (PowLoc.union dst_uses api_uses.src) du_map
      in
      process_arg_def node pid mem is_full tail_typs tail_exps api_uses du_map
  | Buf _ :: tail_typs, exp :: tail_exps ->
      let buf_defs = ItvSem.eval_lv pid (Cil.Mem exp, Cil.NoOffset) mem in
      let buf_uses = use_of_lv pid (Cil.Mem exp, Cil.NoOffset) mem is_full in
      add_assign buf_defs buf_uses du_map
      |> process_arg_def node pid mem is_full tail_typs tail_exps api_uses
  | StructPtr :: tail_typs, exp :: tail_exps ->
      let str_defs = ItvSem.eval_lv pid (Cil.Mem exp, Cil.NoOffset) mem in
      let str_uses = use_of_lv pid (Cil.Mem exp, Cil.NoOffset) mem is_full in
      let new_loc =
        BasicDom.Allocsite.allocsite_of_node node |> Loc.of_allocsite
      in
      add_assign str_defs str_uses du_map
      |> add_assign (PowLoc.singleton new_loc) PowLoc.empty
      |> process_arg_def node pid mem is_full tail_typs tail_exps api_uses
  | _ :: tail_typs, _ :: tail_exps ->
      process_arg_def node pid mem is_full tail_typs tail_exps api_uses du_map

(* Update def-use map to reflect the execution of "[lv] = fname()" *)
let handle_encoded node pid mem is_full lv_locs lv_uses arg_exps fname du_map =
  let api_encoding = ApiMap.find fname api_map in
  let arg_typs = api_encoding.arg_typs in
  let ret_typ = api_encoding.ret_typ in
  let api_uses = collect_uses pid mem is_full arg_typs arg_exps empty_uses in
  process_ret_def lv_locs lv_uses ret_typ api_uses du_map
  |> process_alloc_ret node ret_typ api_uses
  |> process_arg_def node pid mem is_full arg_typs arg_exps api_uses

(* Update def-use map to reflect the execution of "[lv] = unknown()" *)
let handle_unknown pid mem is_full lv_locs lv_uses arg_exps du_map =
  let arg_uses = List.map (fun e -> use_of_exp pid e mem is_full) arg_exps in
  let uses =
    list_fold PowLoc.union arg_uses PowLoc.empty |> PowLoc.union lv_uses
  in
  add_assign lv_locs uses du_map

(* Evaluate abslocs defined and used in the given node. Return them in a mapping
 * to record which abslocs were used to define each absloc. *)
let eval_def_use_internal global mem node =
  let is_full = !Options.full_slice in
  let pid = Node.get_pid node in
  let du_map = DefUseMap.empty in
  match InterCfg.cmdof global.Global.icfg node with
  | IntraCfg.Cmd.Cset (lv, e, _) ->
      let lv_locs = ItvSem.eval_lv pid lv mem in
      let lv_uses = use_of_lv pid lv mem is_full in
      let exp_uses = use_of_exp pid e mem is_full in
      add_assign lv_locs (PowLoc.union lv_uses exp_uses) du_map
  | IntraCfg.Cmd.Cexternal (lv, _) -> (
      match Cil.typeOfLval lv with
      | Cil.TInt (_, _) | Cil.TFloat (_, _) ->
          let lv_locs = ItvSem.eval_lv pid lv mem in
          let lv_uses = use_of_lv pid lv mem is_full in
          add_assign lv_locs lv_uses du_map
      | _ ->
          let lv_locs = ItvSem.eval_lv pid lv mem in
          let lv_uses = use_of_lv pid lv mem is_full in
          let allocsite = BasicDom.Allocsite.allocsite_of_ext None in
          let ext_locs = PowLoc.singleton (Loc.of_allocsite allocsite) in
          add_assign lv_locs lv_uses du_map |> add_assign ext_locs PowLoc.empty)
  | IntraCfg.Cmd.Calloc (lv, IntraCfg.Cmd.Array size_exp, _, _, _) ->
      let lv_locs = ItvSem.eval_lv pid lv mem in
      let lv_uses = use_of_lv pid lv mem is_full in
      let size_uses = use_of_exp pid size_exp mem is_full in
      add_assign lv_locs (PowLoc.union lv_uses size_uses) du_map
  | IntraCfg.Cmd.Calloc (lv, IntraCfg.Cmd.Struct _, _, _, _) ->
      let lv_locs = ItvSem.eval_lv pid lv mem in
      let lv_uses = use_of_lv pid lv mem is_full in
      add_assign lv_locs lv_uses du_map
  (* String and function declarations are not our interest *)
  | IntraCfg.Cmd.Csalloc _ | IntraCfg.Cmd.Cfalloc _ -> du_map
  (* We will consider 'assume' as not defining any absloc *)
  | IntraCfg.Cmd.Cassume _ -> du_map
  (* Undefined or encoded library functions *)
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, _)
    when Global.is_undef f.vname global || ApiMap.mem f.vname api_map ->
      let lv_locs, lv_uses =
        match lvo with
        | None -> (PowLoc.empty, PowLoc.empty)
        | Some lv -> (ItvSem.eval_lv pid lv mem, use_of_lv pid lv mem is_full)
      in
      let fn = f.vname in
      if ApiMap.mem fn api_map then
        handle_encoded node pid mem is_full lv_locs lv_uses arg_exps fn du_map
      else handle_unknown pid mem is_full lv_locs lv_uses arg_exps du_map
  (* User-defined functions *)
  | IntraCfg.Cmd.Ccall (_, f, arg_exps, _) ->
      let arg_uses_list =
        List.map (fun e -> use_of_exp pid e mem is_full) arg_exps
      in
      let fs = ItvSem.eval_callees pid f global mem in
      let folder f acc_du_map =
        let arg_list =
          InterCfg.argsof global.icfg f
          |> List.map (fun x -> Loc.of_lvar f x.Cil.vname x.Cil.vtype)
        in
        add_arg_assigns arg_list arg_uses_list acc_du_map
      in
      PowProc.fold folder fs du_map
  | IntraCfg.Cmd.Creturn (None, _) -> du_map
  | IntraCfg.Cmd.Creturn (Some e, _) ->
      (* Analysis semantics is weak update, but in slicing we don't have to *)
      let defs = Loc.return_var pid (Cil.typeOf e) |> PowLoc.singleton in
      let uses = use_of_exp pid e mem is_full in
      add_assign defs uses du_map
  | IntraCfg.Cmd.Cskip _ when InterCfg.is_returnnode node global.icfg -> (
      let callnode = InterCfg.callof node global.icfg in
      match InterCfg.cmdof global.icfg callnode with
      | IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
          let lv_locs = ItvSem.eval_lv pid lv mem in
          let lv_uses = use_of_lv pid lv mem is_full in
          let callees = ItvSem.eval_callees pid f global mem in
          let ret_vars =
            PowProc.fold
              (fun f ->
                let ret = Loc.return_var f (Cil.typeOfLval lv) in
                PowLoc.add ret)
              callees PowLoc.empty
          in
          (* Don't think this has to be weak update always *)
          add_assign lv_locs (PowLoc.union lv_uses ret_vars) du_map
      | _ -> du_map)
  | IntraCfg.Cmd.Cskip _ -> du_map
  | IntraCfg.Cmd.Casm _ -> du_map
  | _ -> invalid_arg "defUse.ml: eval_def_use_internal"

let memoize_table = Hashtbl.create 100000

let eval_def_use global mem node =
  if Hashtbl.mem memoize_table node then Hashtbl.find memoize_table node
  else
    let du_map = eval_def_use_internal global mem node in
    let du_info = DefUseInfo.make du_map in
    let _ = Hashtbl.replace memoize_table node du_info in
    du_info

(* Evaluate abslocs used in target node. *)
let eval_use_of_targ global mem node =
  let pid = Node.get_pid node in
  match InterCfg.cmdof global.Global.icfg node with
  | IntraCfg.Cmd.Cset (lv, e, _) ->
      (* In the target node, we will consider abslocs used to evaluate 'lv'. For
       * example, if we have "*p = 0", we will trace data-flows on 'p'. *)
      let lv_uses = use_of_lv pid lv mem true in
      let e_uses = use_of_exp pid e mem true in
      PowLoc.join lv_uses e_uses
  | IntraCfg.Cmd.Cexternal _ -> failwith "eval_use_of_targ: TODO"
  | IntraCfg.Cmd.Calloc (lv, IntraCfg.Cmd.Array size_exp, _, _, _) ->
      let lv_uses = use_of_lv pid lv mem true in
      let e_uses = use_of_exp pid size_exp mem true in
      PowLoc.join lv_uses e_uses
  | IntraCfg.Cmd.Calloc (lv, IntraCfg.Cmd.Struct _, _, _, _) ->
      use_of_lv pid lv mem true
  (* String and function declarations are not our interest *)
  | IntraCfg.Cmd.Csalloc _ | IntraCfg.Cmd.Cfalloc _ -> PowLoc.empty
  | IntraCfg.Cmd.Cassume (e, _, _) -> use_of_exp pid e mem true
  (* Encoded library functions *)
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, _)
    when ApiMap.mem f.vname api_map -> (
      let api_encoding = ApiMap.find f.vname api_map in
      let arg_typs = api_encoding.arg_typs in
      let api_uses = collect_uses pid mem true arg_typs arg_exps empty_uses in
      let all_arg_uses =
        PowLoc.union api_uses.src api_uses.dst
        |> PowLoc.union api_uses.buf |> PowLoc.union api_uses.size
      in
      match lvo with
      | None -> all_arg_uses
      | Some lv -> PowLoc.union all_arg_uses (use_of_lv pid lv mem true))
  (* Undefined library functions or user-defined functions *)
  | IntraCfg.Cmd.Ccall (lvo, _, arg_exps, _) -> (
      let arg_uses = List.map (fun e -> use_of_exp pid e mem true) arg_exps in
      let uses = list_fold PowLoc.union arg_uses PowLoc.empty in
      match lvo with
      | None -> uses
      | Some lv -> PowLoc.union uses (use_of_lv pid lv mem true))
  | IntraCfg.Cmd.Creturn (None, _) -> PowLoc.empty
  | IntraCfg.Cmd.Creturn (Some e, _) -> use_of_exp pid e mem true
  (* Handle all Cskip (including return nodes) commands as empty use. *)
  | IntraCfg.Cmd.Cskip _ -> PowLoc.empty
  | IntraCfg.Cmd.Casm _ -> PowLoc.empty
  | _ -> invalid_arg "defUse.ml: eval_use_of_targ"

module S = struct
  include ItvSem
  module Access = ItvSem.Dom.Access

  let accessof ?locset:(_ = ItvSem.Dom.PowA.empty) global node _ mem =
    let du_info = eval_def_use global mem node in
    let targets = get_target_nodes () in
    let uses =
      if InterCfg.NodeSet.mem node targets then eval_use_of_targ global mem node
      else du_info.uses
    in
    Access.Info.add_set Access.Info.def du_info.defs Access.Info.empty
    |> Access.Info.add_set Access.Info.use uses
end
