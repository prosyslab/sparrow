open Vocab
open ProsysCil
open Cil
open AbsSem
open BasicDom
open Global
open TaintDom
open ApiSem
module Dom = TaintDom.Mem
module Access = Dom.Access
module Spec = Spec.Make (Dom)

let can_strong_update mode global lvs =
  match (mode, lvs) with
  | Weak, _ -> false
  | Strong, lvs' ->
      if PowLoc.cardinal lvs' = 1 then
        let lv = PowLoc.choose lvs' in
        Loc.is_gvar lv
        || (Loc.is_lvar lv && not (Global.is_rec (Loc.get_proc lv) global))
      else false

let lookup locs mem = Mem.lookup locs mem

let update mode global locs v mem =
  if can_strong_update mode global locs then Mem.strong_update locs v mem
  else Mem.weak_update locs v mem

let inspect_overflow v1 v2 itv1 itv2 =
  match (v1.Val.int_overflow, v2.Val.int_overflow) with
  | IntOverflow.Top, _ | _, IntOverflow.Top -> IntOverflow.top
  | _, _ ->
      let x_taint_inf =
        Itv.is_infinite itv1 && UserInput.is_taint v1.Val.user_input
      in
      let y_taint_inf =
        Itv.is_infinite itv2 && UserInput.is_taint v2.Val.user_input
      in
      if x_taint_inf || y_taint_inf then IntOverflow.top else IntOverflow.bot

let eval_bop b v1 v2 itv1 itv2 =
  match b with
  | Cil.PlusA | Cil.MinusA | Cil.Mult | Cil.PlusPI | Cil.IndexPI | Cil.MinusPI
  | Cil.MinusPP | Cil.Div | Cil.Shiftlt | Cil.Shiftrt | Cil.Mod | Cil.BAnd
  | Cil.BXor | Cil.BOr ->
      (* overflow may happen *)
      let user_input = UserInput.join v1.Val.user_input v2.Val.user_input in
      let int_overflow = inspect_overflow v1 v2 itv1 itv2 in
      { Val.int_overflow; user_input }
  | Cil.Lt | Cil.Gt | Cil.Le | Cil.Ge | Cil.Eq | Cil.Ne | Cil.LAnd | Cil.LOr ->
      Val.bot

let rec resolve_offset pid offset itvmem mem =
  match offset with
  | Cil.NoOffset -> ()
  | Cil.Field (_, o) -> resolve_offset pid o itvmem mem
  | Cil.Index (e, o) ->
      let _ = eval pid e itvmem mem in
      resolve_offset pid o itvmem mem

and eval_lv pid lv itvmem mem =
  (match fst lv with
  | Cil.Mem e ->
      let _ = eval pid e itvmem mem in
      ()
  | _ -> ());
  resolve_offset pid (snd lv) itvmem mem

and eval pid e itvmem mem =
  match e with
  | Cil.Const _ | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ | Cil.AlignOf _
  | Cil.AlignOfE _
  | Cil.UnOp (_, _, _)
  | Cil.AddrOf _ | Cil.AddrOfLabel _ | Cil.StartOf _ ->
      Val.bot
  | Cil.Lval l ->
      (* for access analysis *)
      eval_lv pid l itvmem mem;
      lookup (ItvSem.eval_lv pid l itvmem) mem
  | Cil.BinOp (b, e1, e2, _) ->
      let itv1, itv2 =
        ( ItvSem.eval pid e1 itvmem |> ItvDom.Val.itv_of_val,
          ItvSem.eval pid e2 itvmem |> ItvDom.Val.itv_of_val )
      in
      eval_bop b (eval pid e1 itvmem mem) (eval pid e2 itvmem mem) itv1 itv2
  | Cil.Question (_, e2, e3, _) ->
      (* pruning *)
      Val.join (eval pid e2 itvmem mem) (eval pid e3 itvmem mem)
  | Cil.CastE (_, e) -> eval pid e itvmem mem

let eval_list pid exps itvmem mem =
  List.map (fun e -> eval pid e itvmem mem) exps

let sparrow_print pid exps itvmem mem loc =
  if !Options.verbose < 1 then ()
  else
    let vs = eval_list pid exps itvmem mem in
    let vs_str = string_of_list Val.to_string vs in
    let exps_str = string_of_list CilHelper.s_exp exps in
    Logging.info "sparrow_print (%s %@ %s) : %s\n" exps_str
      (CilHelper.s_location loc) vs_str

(* argc, argv *)
let sparrow_arg mode node exps loc itvmem (mem, global) =
  match exps with
  | Cil.Lval argc :: Cil.Lval _ :: _ ->
      let argv_a = Allocsite.allocsite_of_ext (Some "argv") in
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      let pid = Node.pid node in
      update mode global
        (ItvSem.eval_lv pid argc itvmem)
        (Val.input_value node loc) mem
      |> update mode global
           (PowLoc.singleton (Loc.of_allocsite argv_a))
           (Val.input_value node loc)
      |> update mode global
           (PowLoc.singleton (Loc.of_allocsite arg_a))
           (Val.input_value node loc)
  | _ -> mem

(* optind, optarg *)
let sparrow_opt mode node exps loc (mem, global) =
  match exps with
  | Cil.Lval _ :: Cil.Lval _ :: _ ->
      let arg_a = Allocsite.allocsite_of_ext (Some "arg") in
      update mode global
        (PowLoc.singleton (Loc.of_allocsite arg_a))
        (Val.input_value node loc) mem
  | _ -> mem

let eval_src src_typ pid itvmem mem arg_e =
  match src_typ with
  | Value -> eval pid arg_e itvmem mem
  | Array ->
      let ploc =
        ItvSem.eval pid arg_e itvmem
        |> ItvDom.Val.array_of_val |> ArrayBlk.pow_loc_of_array
      in
      lookup ploc mem

let rec collect_src_vals arg_exps arg_typs pid itvmem mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ Src (Variable, src_typ) ] ->
      List.map (eval_src src_typ pid itvmem mem) arg_exps
  | _, Src (Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, Src (Fixed, src_typ) :: arg_typs_left ->
      let src_v = eval_src src_typ pid itvmem mem arg_e in
      src_v :: collect_src_vals arg_exps_left arg_typs_left pid itvmem mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_src_vals arg_exps_left arg_typs_left pid itvmem mem

let rec collect_dst_vals arg_exps arg_typs pid itvmem mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ Dst (Variable, _) ] ->
      List.map (fun e -> eval pid e itvmem mem) arg_exps
  | _, Dst (Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, Dst (Fixed, _) :: arg_typs_left ->
      let dst_v = eval pid arg_e itvmem mem in
      dst_v :: collect_dst_vals arg_exps_left arg_typs_left pid itvmem mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_dst_vals arg_exps_left arg_typs_left pid itvmem mem

let rec collect_buf_vals arg_exps arg_typs pid itvmem mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | _, [ Buf (Variable, _) ] ->
      List.map (fun e -> eval pid e itvmem mem) arg_exps
  | _, Buf (Variable, _) :: _ ->
      failwith "itvSem.ml : API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, Buf (Fixed, _) :: arg_typs_left ->
      let buf_v = eval pid arg_e itvmem mem in
      buf_v :: collect_buf_vals arg_exps_left arg_typs_left pid itvmem mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_buf_vals arg_exps_left arg_typs_left pid itvmem mem

let rec collect_size_vals arg_exps arg_typs node itvmem mem =
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> []
  | arg_e :: arg_exps_left, Size :: arg_typs_left ->
      let size_v = eval node arg_e itvmem mem in
      size_v :: collect_size_vals arg_exps_left arg_typs_left node itvmem mem
  | _ :: arg_exps_left, _ :: arg_typs_left ->
      collect_size_vals arg_exps_left arg_typs_left node itvmem mem

let process_dst mode node pid src_vals global alloc itvmem mem dst_e =
  let src_v = List.fold_left Val.join Val.bot src_vals in
  let dst_loc = ItvDom.Val.all_locs (ItvSem.eval pid dst_e itvmem) in
  if alloc then
    let allocsite = Allocsite.allocsite_of_node node in
    let loc = PowLoc.singleton @@ Loc.of_allocsite allocsite in
    update mode global loc src_v mem
  else update mode global dst_loc src_v mem

let process_buf mode node global loc itvmem mem dst_e =
  let pid = Node.pid node in
  let buf_loc = ItvDom.Val.all_locs (ItvSem.eval pid dst_e itvmem) in
  update mode global buf_loc (Val.input_value node loc) mem

let rec process_args mode node arg_exps arg_typs src_vals loc itvmem
    (mem, global) =
  let va_src_flag =
    List.exists (function Src (Variable, _) -> true | _ -> false) arg_typs
  in
  let pid = Node.pid node in
  match (arg_exps, arg_typs) with
  | [], _ | _, [] -> mem
  | _, [ Dst (Variable, alloc) ] ->
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      List.fold_left
        (process_dst mode node pid src_vals global alloc itvmem)
        mem arg_exps
  | _, Dst (Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, Dst (Fixed, alloc) :: arg_typs_left ->
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      let mem =
        process_dst mode node pid src_vals global alloc itvmem mem arg_e
      in
      process_args mode node arg_exps_left arg_typs_left src_vals loc itvmem
        (mem, global)
  | _, [ Buf (Variable, _) ] ->
      List.fold_left (process_buf mode node global loc itvmem) mem arg_exps
  | _, Buf (Variable, _) :: _ ->
      failwith "API encoding error (Varg not at the last position)"
  | arg_e :: arg_exps_left, Buf (Fixed, _) :: arg_typs_left ->
      let mem = process_buf mode node global loc itvmem mem arg_e in
      process_args mode node arg_exps_left arg_typs_left src_vals loc itvmem
        (mem, global)
  | _ :: arg_exps_left, Src _ :: arg_typs_left
  | _ :: arg_exps_left, Size :: arg_typs_left
  | _ :: arg_exps_left, Skip :: arg_typs_left ->
      process_args mode node arg_exps_left arg_typs_left src_vals loc itvmem
        (mem, global)
  | _, _ -> mem

let gen_block mode node init_v (mem, global) =
  let allocsite = Allocsite.allocsite_of_node node in
  let pow_loc = PowLoc.singleton (Loc.of_allocsite allocsite) in
  (update mode global pow_loc init_v mem, Val.bot)

let produce_ret mode node ret_typ va_src_flag src_vals dst_vals buf_vals
    size_vals loc (mem, global) =
  match ret_typ with
  | Const -> (mem, Val.bot)
  | TaintInput ->
      (* User input value (top itv & taintness) *)
      (mem, Val.input_value node loc)
  | SrcArg ->
      (* Src argument returned *)
      let _ = assert (List.length src_vals = 1) in
      (mem, List.hd src_vals)
  | SizeArg ->
      (* Integer between 0 ~ Size argument returned *)
      let _ = assert (List.length size_vals = 1) in
      (mem, List.hd size_vals)
  | TopWithSrcTaint ->
      (* Top itv & taintness of Src argument returned *)
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      let src_v = List.fold_left Val.join Val.bot src_vals in
      (mem, src_v)
  | DstArg ->
      (* Dst argument returned *)
      let _ = assert (List.length dst_vals = 1) in
      (mem, List.hd dst_vals)
  | BufArg ->
      (* Buf argument returned *)
      let _ = assert (List.length buf_vals = 1) in
      (mem, List.hd buf_vals)
  | AllocConst ->
      (* New block, filled with given abstract val. *)
      gen_block mode node Val.bot (mem, global)
  | AllocDst ->
      (* New block, filled with Src argument *)
      let _ = assert (va_src_flag || List.length src_vals > 0) in
      let src_v = List.fold_left Val.join Val.bot src_vals in
      gen_block mode node src_v (mem, global)
  | AllocBuf ->
      (* New block, filled with user input *)
      gen_block mode node (Val.input_value node loc) (mem, global)
  | AllocStruct ->
      (* Newly allocated struct *)
      gen_block mode node (Val.input_value node loc) (mem, global)

let handle_api mode node (lvo, exps) itvmem (mem, global) api_type loc =
  let pid = Node.pid node in
  let arg_typs = api_type.ApiSem.arg_typs in
  let ret_typ = api_type.ApiSem.ret_typ in
  let src_vals = collect_src_vals exps arg_typs pid itvmem mem in
  let dst_vals = collect_dst_vals exps arg_typs pid itvmem mem in
  let buf_vals = collect_buf_vals exps arg_typs pid itvmem mem in
  let size_vals = collect_size_vals exps arg_typs pid itvmem mem in
  let mem =
    process_args mode node exps arg_typs src_vals loc itvmem (mem, global)
  in
  match lvo with
  | Some lv ->
      let va_src_flag =
        List.exists (function Src (Variable, _) -> true | _ -> false) arg_typs
      in
      let mem, ret_v =
        produce_ret mode node ret_typ va_src_flag src_vals dst_vals buf_vals
          size_vals loc (mem, global)
      in
      update mode global (ItvSem.eval_lv pid lv itvmem) ret_v mem
  | None -> mem

let is_printf0 fname = fname = "printf"

let is_printf1 fname =
  List.mem fname
    [
      "fprintf";
      "sprintf";
      "vfprintf";
      "vsprintf";
      "vasprintf";
      "__asprintf";
      "asprintf";
      "vdprintf";
      "dprintf";
      "easprintf";
      "evasprintf";
    ]

let is_printf2 fname = List.mem fname [ "snprintf"; "vsnprintf" ]
let is_printf fname = is_printf0 fname || is_printf1 fname || is_printf2 fname

let dummy_read_printf fname pid exps itvmem mem =
  let typ = if is_printf0 fname then 0 else if is_printf1 fname then 1 else 2 in
  let locs = ItvDom.Val.all_locs (ItvSem.eval pid (List.nth exps typ) itvmem) in
  (* for inspection *)
  let _ = lookup locs mem in
  ()

let sparrow_dump mem loc =
  if !Options.verbose < 1 then ()
  else
    Logging.info "sparrow_dump (%s) : \n%a\n" (CilHelper.s_location loc) Mem.pp
      mem

let handle_undefined_functions mode node (lvo, f, exps) itvmem (mem, global) loc
    =
  let pid = Node.pid node in
  match f.vname with
  | "sparrow_arg" -> sparrow_arg mode node exps loc itvmem (mem, global)
  (*   | "sparrow_opt" -> sparrow_opt mode node exps loc itvmem (mem,global) *)
  | "sparrow_print" ->
      sparrow_print pid exps itvmem mem loc;
      mem
  | "sparrow_dump" ->
      sparrow_dump mem loc;
      mem
  | fname when ApiSem.ApiMap.mem fname ApiSem.api_map ->
      if is_printf fname then dummy_read_printf fname pid exps itvmem mem;
      let api_type = ApiSem.ApiMap.find fname ApiSem.api_map in
      handle_api mode node (lvo, exps) itvmem (mem, global) api_type loc
  | fname when is_printf fname ->
      if is_printf fname then dummy_read_printf fname pid exps itvmem mem;
      mem
  | _ -> mem

let bind_lvar mode global lvar v mem =
  let l = PowLoc.singleton lvar in
  update mode global l v mem

let bind_arg_ids mode global vs arg_ids mem =
  list_fold2_prefix (bind_lvar mode global) arg_ids vs mem

(* Binds a list of values to a set of argument lists.  If |args_set|
    > 1, the argument binding does weak update. *)
let bind_arg_lvars_set mode global arg_ids_set vs mem =
  let mode = if BatSet.cardinal arg_ids_set > 1 then AbsSem.Weak else mode in
  BatSet.fold (bind_arg_ids mode global vs) arg_ids_set mem

let run_cmd mode node itvmem (mem, global) =
  let pid = Node.pid node in
  match InterCfg.cmd_of global.icfg node with
  | IntraCfg.Cmd.Cset (l, e, _) ->
      let lv = ItvSem.eval_lv pid l itvmem in
      update mode global lv (eval pid e itvmem mem) mem
  | IntraCfg.Cmd.Cexternal (_, _) -> mem
  | IntraCfg.Cmd.Calloc (_, IntraCfg.Cmd.Array e, _, _, _) ->
      let _ = eval pid e itvmem mem in
      (* for inspection *)
      mem
  | IntraCfg.Cmd.Calloc (_, IntraCfg.Cmd.Struct _, _, _, _) -> mem
  | IntraCfg.Cmd.Csalloc (_, _, _) -> mem
  | IntraCfg.Cmd.Cfalloc (_, _, _) | IntraCfg.Cmd.Cassume (_, _, _) -> mem
  | IntraCfg.Cmd.Ccall (lvo, Cil.Lval (Cil.Var f, Cil.NoOffset), arg_exps, loc)
    when Global.is_undef f.vname global
         || ApiSem.ApiMap.mem f.vname ApiSem.api_map ->
      (* undefined library functions *)
      let _ = eval_list pid arg_exps itvmem mem in
      (* for inspection *)
      handle_undefined_functions mode node (lvo, f, arg_exps) itvmem
        (mem, global) loc
  | IntraCfg.Cmd.Ccall (_, f, arg_exps, _) ->
      (* user functions *)
      let fs = ItvSem.eval_callees pid f global itvmem in
      if PowProc.eq fs PowProc.bot then mem
      else
        let arg_lvars_of_proc f acc =
          let args = InterCfg.args_of global.icfg f in
          let lvars =
            List.map (fun x -> Loc.of_lvar f x.Cil.vname x.Cil.vtype) args
          in
          BatSet.add lvars acc
        in
        let arg_lvars_set = PowProc.fold arg_lvars_of_proc fs BatSet.empty in
        let arg_vals = eval_list pid arg_exps itvmem mem in
        bind_arg_lvars_set mode global arg_lvars_set arg_vals mem
  | IntraCfg.Cmd.Creturn (None, _) -> mem
  | IntraCfg.Cmd.Creturn (Some e, _) ->
      update Weak global
        (Loc.return_var pid (Cil.typeOf e) |> PowLoc.singleton)
        (eval pid e itvmem mem) mem
  | IntraCfg.Cmd.Cskip _ when InterCfg.is_return_node node global.icfg -> (
      let callnode = InterCfg.call_of node global.icfg in
      match InterCfg.cmd_of global.icfg callnode with
      | IntraCfg.Cmd.Ccall (Some lv, f, _, _) ->
          let callees = ItvSem.eval_callees pid f global itvmem in
          let retvar_set =
            PowProc.fold
              (fun f ->
                let ret = Loc.return_var f (Cil.typeOfLval lv) in
                PowLoc.add ret)
              callees PowLoc.empty
          in
          update Weak global
            (ItvSem.eval_lv pid lv itvmem)
            (lookup retvar_set mem) mem
      | _ -> mem)
  | IntraCfg.Cmd.Cskip _ -> mem
  | IntraCfg.Cmd.Casm _ -> mem
  | _ -> invalid_arg "taintSem.ml: run"

let run mode spec node (mem, global) =
  let itvmem = ItvDom.Table.find node spec.Spec.ptrinfo in
  let mem = run_cmd mode node itvmem (mem, global) in
  (mem, global)

let initial _ = Dom.bot
