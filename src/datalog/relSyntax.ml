open IntraCfg
open Cmd
module Cil = ProsysCil.Cil
module F = Format
module Node = InterCfg.Node

type formatter = {
  (* Function body *)
  func : F.formatter;
  (* Command *)
  entry : F.formatter;
  exit : F.formatter;
  join : F.formatter;
  skip : F.formatter;
  assign : F.formatter;
  assume : F.formatter;
  alloc : F.formatter;
  salloc : F.formatter;
  call : F.formatter;
  libcall : F.formatter;
  arg : F.formatter;
  return : F.formatter;
  cmd : F.formatter;
  (* Cmd for Patron *)
  set : F.formatter;
  alloc_exp : F.formatter;
  salloc_exp : F.formatter;
  call_exp : F.formatter;
  readcall_exp : F.formatter;
  libcall_exp : F.formatter;
  real_lv : F.formatter;
  (* Expressions *)
  const_exp : F.formatter;
  lval_exp : F.formatter;
  binop_exp : F.formatter;
  unop_exp : F.formatter;
  cast_exp : F.formatter;
  sizeof_exp : F.formatter;
  other_exp : F.formatter;
  global_var : F.formatter;
  local_var : F.formatter;
  field : F.formatter;
  st_fld : F.formatter;
  index : F.formatter;
  lval : F.formatter;
  mem : F.formatter;
  start_of : F.formatter;
  addr_of : F.formatter;
  (* BinOp *)
  binop : F.formatter;
  plusa : F.formatter;
  pluspi : F.formatter;
  indexpi : F.formatter;
  minusa : F.formatter;
  minuspi : F.formatter;
  minuspp : F.formatter;
  mult : F.formatter;
  div : F.formatter;
  modd : F.formatter;
  shiftlt : F.formatter;
  shiftrt : F.formatter;
  lt : F.formatter;
  gt : F.formatter;
  le : F.formatter;
  ge : F.formatter;
  eq : F.formatter;
  ne : F.formatter;
  band : F.formatter;
  bxor : F.formatter;
  bor : F.formatter;
  landd : F.formatter;
  lorr : F.formatter;
  (* UnOp *)
  unop : F.formatter;
  bnot : F.formatter;
  lnot : F.formatter;
  neg : F.formatter;
  (* Sems for Patron *)
  evallv : F.formatter;
  allocpath : F.formatter;
  readpath : F.formatter;
}

let binop_count = ref 0
let binop_map = Hashtbl.create 1000

let new_binop_id bop =
  let id = "BinOp-" ^ string_of_int !binop_count in
  binop_count := !binop_count + 1;
  Hashtbl.add binop_map bop id;
  id

let unop_count = ref 0
let unop_map = Hashtbl.create 1000

let new_unop_id uop =
  let id = "UnOp-" ^ string_of_int !unop_count in
  binop_count := !binop_count + 1;
  Hashtbl.add unop_map uop id;
  id

let exp_count = ref 0
let exp_map = Hashtbl.create 1000

let new_exp_id e =
  let id = "Exp-" ^ string_of_int !exp_count in
  exp_count := !exp_count + 1;
  Hashtbl.add exp_map e id;
  id

let alloc_count = ref 0
let alloc_map = Hashtbl.create 1000

let new_alloc_id e =
  let id = "AllocExp-" ^ string_of_int !alloc_count in
  alloc_count := !alloc_count + 1;
  Hashtbl.add alloc_map e id;
  id

let salloc_count = ref 0
let salloc_map = Hashtbl.create 1000

let new_salloc_id e =
  let id = "SallocExp-" ^ string_of_int !salloc_count in
  salloc_count := !salloc_count + 1;
  Hashtbl.add salloc_map e id;
  id

let call_count = ref 0
let call_map = Hashtbl.create 1000

let new_call_id e =
  let id = "CallExp-" ^ string_of_int !call_count in
  call_count := !call_count + 1;
  Hashtbl.add call_map e id;
  id

let libcall_count = ref 0
let libcall_map = Hashtbl.create 1000

let new_libcall_id e =
  let id = "LibCallExp-" ^ string_of_int !libcall_count in
  libcall_count := !libcall_count + 1;
  Hashtbl.add libcall_map e id;
  id

let readcall_count = ref 0
let readcall_map = Hashtbl.create 1000

let new_readcall_id e =
  let id = "ReadCallExp-" ^ string_of_int !readcall_count in
  readcall_count := !readcall_count + 1;
  Hashtbl.add readcall_map e id;
  id

let readpath_count = ref 0
let readpath_map : (Node.t * Node.t, string) Hashtbl.t = Hashtbl.create 1000

let new_readpath_id n1 n2 =
  let id = "ReadPath-" ^ string_of_int !readpath_count in
  readpath_count := !readpath_count + 1;
  Hashtbl.add readpath_map (n1, n2) id

let allocpath_count = ref 0
let allocpath_map : (Node.t * Node.t, string) Hashtbl.t = Hashtbl.create 1000

let new_allocpath_id n1 n2 =
  let id = "AllocPath-" ^ string_of_int !allocpath_count in
  allocpath_count := !allocpath_count + 1;
  Hashtbl.add allocpath_map (n1, n2) id

let lv_count = ref 0
let lv_map = Hashtbl.create 1000

let new_lv_id lv =
  let id = "Lval-" ^ string_of_int !lv_count in
  lv_count := !lv_count + 1;
  Hashtbl.add lv_map lv id;
  id

let donotcare_lv =
  let vi = Cil.makeGlobalVar "__DONOTCARE__" Cil.voidType in
  (Cil.Var vi, Cil.NoOffset)

let string_of_bop = function
  | Cil.PlusA -> "PlusA"
  | PlusPI -> "PlusPI"
  | IndexPI -> "IndexPI"
  | MinusA -> "MinusA"
  | MinusPI -> "MinusPI"
  | MinusPP -> "MinusPP"
  | Mult -> "Mult"
  | Div -> "Div"
  | Mod -> "Mod"
  | Shiftlt -> "bvshl"
  | Shiftrt -> "bvshr"
  | Lt -> "Lt"
  | Gt -> "Gt"
  | Le -> "Le"
  | Ge -> "Ge"
  | Eq -> "Eq"
  | Ne -> "Ne"
  | BAnd -> "bvand"
  | BXor -> "bvxor"
  | BOr -> "bvor"
  | LAnd -> "and"
  | LOr -> "or"

let pp_binop fmt bop =
  if Hashtbl.mem binop_map bop then ()
  else
    let id = new_binop_id bop in
    F.fprintf fmt.binop "%s\t%s\n" id (string_of_bop bop);
    match bop with
    | Cil.PlusA -> F.fprintf fmt.plusa "%s\n" id
    | PlusPI -> F.fprintf fmt.pluspi "%s\n" id
    | IndexPI -> F.fprintf fmt.indexpi "%s\n" id
    | MinusA -> F.fprintf fmt.minusa "%s\n" id
    | MinusPI -> F.fprintf fmt.minuspi "%s\n" id
    | MinusPP -> F.fprintf fmt.minuspp "%s\n" id
    | Mult -> F.fprintf fmt.mult "%s\n" id
    | Div -> F.fprintf fmt.div "%s\n" id
    | Mod -> F.fprintf fmt.modd "%s\n" id
    | Shiftlt -> F.fprintf fmt.shiftlt "%s\n" id
    | Shiftrt -> F.fprintf fmt.shiftrt "%s\n" id
    | Lt -> F.fprintf fmt.lt "%s\n" id
    | Gt -> F.fprintf fmt.gt "%s\n" id
    | Le -> F.fprintf fmt.le "%s\n" id
    | Ge -> F.fprintf fmt.ge "%s\n" id
    | Eq -> F.fprintf fmt.eq "%s\n" id
    | Ne -> F.fprintf fmt.ne "%s\n" id
    | BAnd -> F.fprintf fmt.band "%s\n" id
    | BXor -> F.fprintf fmt.bxor "%s\n" id
    | BOr -> F.fprintf fmt.bor "%s\n" id
    | LAnd -> F.fprintf fmt.landd "%s\n" id
    | LOr -> F.fprintf fmt.lorr "%s\n" id

let string_of_uop = function
  | Cil.BNot -> "BNot"
  | LNot -> "LNot"
  | Neg -> "Neg"

let pp_unop fmt uop =
  if Hashtbl.mem unop_map uop then ()
  else
    let id = new_unop_id uop in
    F.fprintf fmt.unop "%s\t%s\n" id (string_of_uop uop);
    match uop with
    | Cil.BNot -> F.fprintf fmt.bnot "%s\n" id
    | LNot -> F.fprintf fmt.lnot "%s\n" id
    | Neg -> F.fprintf fmt.neg "%s\n" id

let rec remove_cast = function
  | ( Cil.Const _ | Cil.Lval _ | Cil.SizeOf _ | Cil.SizeOfStr _ | Cil.AlignOf _
    | Cil.AddrOf _ | Cil.AddrOfLabel _ | Cil.StartOf _ ) as e ->
      e
  | Cil.SizeOfE e -> Cil.SizeOfE (remove_cast e)
  | Cil.AlignOfE e -> Cil.AlignOfE (remove_cast e)
  | Cil.UnOp (o, e, t) -> Cil.UnOp (o, remove_cast e, t)
  | Cil.BinOp (o, e1, e2, t) -> Cil.BinOp (o, remove_cast e1, remove_cast e2, t)
  | Cil.Question (e1, e2, e3, t) ->
      Cil.Question (remove_cast e1, remove_cast e2, remove_cast e3, t)
  | Cil.CastE (_, e) -> remove_cast e

let rec pp_lv fmt n lv =
  if Hashtbl.mem lv_map lv then ()
  else
    let id = new_lv_id lv in
    match lv with
    | Cil.Var vi, Cil.NoOffset ->
        if vi.Cil.vglob then F.fprintf fmt.global_var "%s\t%s\n" id vi.vname
        else F.fprintf fmt.local_var "%s\t%s\n" id vi.vname
    | Cil.Var _, Cil.Field (_, _) -> F.fprintf fmt.field "%s\n" id
    | Cil.Mem e, offset ->
        pp_exp fmt n e;
        (match offset with
        | Cil.Field (_, _) -> F.fprintf fmt.field "%s\n" id
        | _ -> ());
        let e_id = Hashtbl.find exp_map e in
        F.fprintf fmt.mem "%s\t%s\n" id e_id
    | _, _ -> F.fprintf fmt.lval "%s\tOther\n" id

and pp_exp fmt n e =
  if Hashtbl.mem exp_map e then ()
  else
    let id = new_exp_id e in
    match e with
    | Cil.Const _ -> F.fprintf fmt.const_exp "%s\n" id
    | Cil.Lval lv ->
        pp_lv fmt n lv;
        let lv_id = Hashtbl.find lv_map lv in
        F.fprintf fmt.lval_exp "%s\t%s\n" id lv_id
    | Cil.BinOp (bop, e1, e2, _) ->
        pp_binop fmt bop;
        pp_exp fmt n e1;
        pp_exp fmt n e2;
        let e1_id = Hashtbl.find exp_map e1 in
        let e2_id = Hashtbl.find exp_map e2 in
        F.fprintf fmt.binop_exp "%s\t%s\t%s\t%s\n" id (string_of_bop bop) e1_id
          e2_id
    | Cil.UnOp (unop, e, _) ->
        pp_exp fmt n e;
        pp_unop fmt unop;
        let e_id = Hashtbl.find exp_map e in
        F.fprintf fmt.unop_exp "%s\t%s\t%s\n" id (string_of_uop unop) e_id
    | Cil.CastE (_, e) ->
        pp_exp fmt n e;
        let e_id = Hashtbl.find exp_map e in
        F.fprintf fmt.cast_exp "%s\t%s\n" id e_id
    | Cil.StartOf l ->
        pp_lv fmt n l;
        let l_id = Hashtbl.find lv_map l in
        F.fprintf fmt.start_of "%s\t%s\n" id l_id;
        F.fprintf fmt.lval_exp "%s\t%s\n" id l_id
    | Cil.SizeOfE e1 ->
        pp_exp fmt n e1;
        let e_id = Hashtbl.find exp_map e1 in
        F.fprintf fmt.sizeof_exp "%s\t%s\n" id e_id
    | _ -> F.fprintf fmt.other_exp "%s\n" id

let arg_count = ref 0

let new_arg_id () =
  let id = "ArgList-" ^ string_of_int !arg_count in
  incr arg_count;
  id

let arg_pos_count = ref 0

let new_arg_pos_id () =
  let id = "Pos-" ^ string_of_int !arg_pos_count in
  incr arg_pos_count;
  id

let pp_arg fmt arg =
  let id = new_arg_id () in
  List.iteri
    (fun _ e ->
      let e' = if !Options.remove_cast then remove_cast e else e in
      Hashtbl.find exp_map e'
      |> F.fprintf fmt.arg "%s\t%s\t%s\n" id (new_arg_pos_id ()))
    arg;
  id

let parse_call_id n e' el' =
  let read_target =
    [
      Str.regexp ".*getuint.*";
      Str.regexp ".*getint.*";
      Str.regexp ".*getfloat.*";
      Str.regexp ".*getdouble.*";
      Str.regexp ".*getc.*";
      Str.regexp ".*getuchar.*";
    ]
  in
  let alloc_target = [ Str.regexp ".*alloc.*" ] in
  if
    List.exists
      (fun re -> Str.string_match re (CilHelper.s_exp e') 0)
      read_target
  then
    if Hashtbl.mem readcall_map (n, e', el') then
      Hashtbl.find readcall_map (n, e', el')
    else new_readcall_id (n, e', el')
  else if
    List.exists
      (fun re -> Str.string_match re (CilHelper.s_exp e') 0)
      alloc_target
  then
    let size = List.hd el' in
    let alloc = Array size in
    if Hashtbl.mem alloc_map alloc then Hashtbl.find alloc_map alloc
    else new_alloc_id alloc
  else if Hashtbl.mem call_map (n, e', el') then
    Hashtbl.find call_map (n, e', el')
  else new_call_id (n, e', el')

let pp_cmd fmt icfg n =
  if InterCfg.pred n icfg |> List.length = 2 then
    F.fprintf fmt.join "%a\n" Node.pp n;
  F.fprintf fmt.func "%s\t%a\n" (Node.get_pid n) Node.pp n;
  match InterCfg.cmdof icfg n with
  | Cskip _ ->
      if InterCfg.is_entry n then F.fprintf fmt.entry "%a\n" Node.pp n
      else if InterCfg.is_exit n then F.fprintf fmt.exit "%a\n" Node.pp n
      else F.fprintf fmt.skip "%a\n" Node.pp n
  | Cset (lv, e, _) ->
      pp_lv fmt n lv;
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let lv_id = Hashtbl.find lv_map lv in
      let e_id = Hashtbl.find exp_map e' in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id e_id;
      F.fprintf fmt.assign "%a\t%s\t%s\n" Node.pp n lv_id e_id
  | Cexternal (_, _) -> F.fprintf fmt.cmd "external\n"
  | Calloc (lv, (Array e as alloc), _, _, _) ->
      pp_lv fmt n lv;
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let lv_id = Hashtbl.find lv_map lv in
      let size_e_id = Hashtbl.find exp_map e' in
      let alloc_id =
        if Hashtbl.mem alloc_map alloc then Hashtbl.find alloc_map alloc
        else new_alloc_id alloc
      in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id alloc_id;
      F.fprintf fmt.alloc_exp "%s\t%s\n" alloc_id size_e_id;
      F.fprintf fmt.alloc "%a\t%s\t%s\n" Node.pp n lv_id size_e_id
  | Calloc (_, _, _, _, _) -> F.fprintf fmt.cmd "alloc\n"
  | Csalloc (lv, str, _) ->
      pp_lv fmt n lv;
      let lv_id = Hashtbl.find lv_map lv in
      let salloc_id =
        if Hashtbl.mem salloc_map str then Hashtbl.find salloc_map str
        else new_salloc_id str
      in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id salloc_id;
      F.fprintf fmt.salloc_exp "%s\t%s\n" salloc_id str;
      F.fprintf fmt.salloc "%a\t%s\n" Node.pp n lv_id
  | Cfalloc (_, _, _) -> F.fprintf fmt.cmd "falloc\n"
  | Ccall (lv_opt, (Lval (Var f, NoOffset) as e), el, _)
    when f.vstorage = Cil.Extern ->
      let lv =
        if Option.is_none lv_opt then donotcare_lv else Option.get lv_opt
      in
      pp_lv fmt n lv;
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let el' =
        List.map (fun e -> if !Options.remove_cast then remove_cast e else e) el
      in
      List.iter (pp_exp fmt n) el';
      let arg_id = pp_arg fmt el' in
      let lv_id = Hashtbl.find lv_map lv in
      let e_id = Hashtbl.find exp_map e' in
      let libcall_id =
        if Hashtbl.mem libcall_map (n, e', el') then
          Hashtbl.find libcall_map (n, e', el')
        else new_libcall_id (n, e', el')
      in
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id libcall_id;
      F.fprintf fmt.libcall_exp "%s\t%s\t%s\n" libcall_id e_id arg_id;
      F.fprintf fmt.libcall "%a\t%s\t%s\t%s\n" Node.pp n lv_id e_id arg_id
  | Ccall (lv_opt, e, el, _) ->
      let lv =
        if Option.is_none lv_opt then donotcare_lv else Option.get lv_opt
      in
      pp_lv fmt n lv;
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let el' =
        List.map (fun e -> if !Options.remove_cast then remove_cast e else e) el
      in
      List.iter (pp_exp fmt n) el';
      let arg_id = pp_arg fmt el' in
      let lv_id = Hashtbl.find lv_map lv in
      let e_id = Hashtbl.find exp_map e' in
      let call_id =
        if Hashtbl.mem call_map (n, e', el') then
          Hashtbl.find call_map (n, e', el')
        else new_call_id (n, e', el')
      in
      F.fprintf fmt.call_exp "%s\t%s\t%s\n" call_id e_id arg_id;
      F.fprintf fmt.set "%a\t%s\t%s\n" Node.pp n lv_id call_id;
      F.fprintf fmt.call "%a\t%s\t%s\t%s\n" Node.pp n lv_id e_id arg_id
  | Creturn (Some e, _) ->
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let id = Hashtbl.find exp_map e' in
      F.fprintf fmt.return "%a\t%s\n" Node.pp n id
  | Cassume (e, _, _) ->
      let e' = if !Options.remove_cast then remove_cast e else e in
      pp_exp fmt n e';
      let e_id = Hashtbl.find exp_map e' in
      F.fprintf fmt.assume "%a\t%s\n" Node.pp n e_id
  | _ -> F.fprintf fmt.cmd "unknown"

let make_formatters dirname =
  let oc_func = open_out (dirname ^ "/Func.facts") in
  let oc_const = open_out (dirname ^ "/ConstExp.facts") in
  let oc_lval = open_out (dirname ^ "/LvalExp.facts") in
  let oc_binop_exp = open_out (dirname ^ "/BinOpExp.facts") in
  let oc_unop_exp = open_out (dirname ^ "/UnOpExp.facts") in
  let oc_cast = open_out (dirname ^ "/CastExp.facts") in
  let oc_sizeof = open_out (dirname ^ "/SizeOfExp.facts") in
  let oc_exp = open_out (dirname ^ "/OtherExp.facts") in
  let oc_cmd = open_out (dirname ^ "/Cmd.facts") in
  let oc_entry = open_out (dirname ^ "/Entry.facts") in
  let oc_exit = open_out (dirname ^ "/Exit.facts") in
  let oc_skip = open_out (dirname ^ "/Skip.facts") in
  let oc_join = open_out (dirname ^ "/Join.facts") in
  let oc_assign = open_out (dirname ^ "/Assign.facts") in
  let oc_assume = open_out (dirname ^ "/Assume.facts") in
  let oc_alloc = open_out (dirname ^ "/Alloc.facts") in
  let oc_salloc = open_out (dirname ^ "/SAlloc.facts") in
  let oc_libcall = open_out (dirname ^ "/LibCall.facts") in
  let oc_call = open_out (dirname ^ "/Call.facts") in
  let oc_arg = open_out (dirname ^ "/Arg.facts") in
  let oc_return = open_out (dirname ^ "/Return.facts") in
  let oc_set = open_out (dirname ^ "/Set.facts") in
  let oc_alloc_exp = open_out (dirname ^ "/AllocExp.facts") in
  let oc_salloc_exp = open_out (dirname ^ "/SAllocExp.facts") in
  let oc_call_exp = open_out (dirname ^ "/CallExp.facts") in
  let oc_libcall_exp = open_out (dirname ^ "/LibCallExp.facts") in
  let oc_readcall_exp = open_out (dirname ^ "/ReadCallExp.facts") in
  let oc_real_lv = open_out (dirname ^ "/RealLv.facts") in
  let oc_global_var = open_out (dirname ^ "/GlobalVar.facts") in
  let oc_local_var = open_out (dirname ^ "/LocalVar.facts") in
  let oc_field = open_out (dirname ^ "/Field.facts") in
  let oc_st_fld = open_out (dirname ^ "/StructField.facts") in
  let oc_index = open_out (dirname ^ "/Index.facts") in
  let oc_lv = open_out (dirname ^ "/Lval.facts") in
  let oc_mem = open_out (dirname ^ "/Mem.facts") in
  let oc_start_of = open_out (dirname ^ "/StartOf.facts") in
  let oc_addr_of = open_out (dirname ^ "/AddrOf.facts") in
  (* BinOp *)
  let oc_binop = open_out (dirname ^ "/Bop.map") in
  let oc_plusa = open_out (dirname ^ "/PlusA.facts") in
  let oc_pluspi = open_out (dirname ^ "/PlusPI.facts") in
  let oc_indexpi = open_out (dirname ^ "/IndexPI.facts") in
  let oc_minusa = open_out (dirname ^ "/MinusA.facts") in
  let oc_minuspi = open_out (dirname ^ "/MinusPI.facts") in
  let oc_minuspp = open_out (dirname ^ "/MinusPP.facts") in
  let oc_mult = open_out (dirname ^ "/Mult.facts") in
  let oc_div = open_out (dirname ^ "/Div.facts") in
  let oc_modd = open_out (dirname ^ "/Mod.facts") in
  let oc_shiftlt = open_out (dirname ^ "/ShiftLt.facts") in
  let oc_shiftrt = open_out (dirname ^ "/ShiftRt.facts") in
  let oc_lt = open_out (dirname ^ "/Lt.facts") in
  let oc_gt = open_out (dirname ^ "/Gt.facts") in
  let oc_le = open_out (dirname ^ "/Le.facts") in
  let oc_ge = open_out (dirname ^ "/Ge.facts") in
  let oc_eq = open_out (dirname ^ "/Eq.facts") in
  let oc_ne = open_out (dirname ^ "/Ne.facts") in
  let oc_band = open_out (dirname ^ "/BAnd.facts") in
  let oc_bxor = open_out (dirname ^ "/BXor.facts") in
  let oc_bor = open_out (dirname ^ "/BOr.facts") in
  let oc_landd = open_out (dirname ^ "/LAnd.facts") in
  let oc_lorr = open_out (dirname ^ "/LOr.facts") in
  (* UnOp *)
  let oc_unop = open_out (dirname ^ "/Uop.map") in
  let oc_bnot = open_out (dirname ^ "/BNot.facts") in
  let oc_lnot = open_out (dirname ^ "/LNot.facts") in
  let oc_neg = open_out (dirname ^ "/Neg.facts") in
  let oc_evallv = open_out (dirname ^ "/EvalLv.facts") in
  let oc_allocpath = open_out (dirname ^ "/AllocPath.facts") in
  let oc_readpath = open_out (dirname ^ "/ReadPath.facts") in
  let fmt =
    {
      func = F.formatter_of_out_channel oc_func;
      entry = F.formatter_of_out_channel oc_entry;
      exit = F.formatter_of_out_channel oc_exit;
      join = F.formatter_of_out_channel oc_join;
      skip = F.formatter_of_out_channel oc_skip;
      assign = F.formatter_of_out_channel oc_assign;
      assume = F.formatter_of_out_channel oc_assume;
      alloc = F.formatter_of_out_channel oc_alloc;
      salloc = F.formatter_of_out_channel oc_salloc;
      libcall = F.formatter_of_out_channel oc_libcall;
      call = F.formatter_of_out_channel oc_call;
      arg = F.formatter_of_out_channel oc_arg;
      return = F.formatter_of_out_channel oc_return;
      cmd = F.formatter_of_out_channel oc_cmd;
      set = F.formatter_of_out_channel oc_set;
      alloc_exp = F.formatter_of_out_channel oc_alloc_exp;
      salloc_exp = F.formatter_of_out_channel oc_salloc_exp;
      call_exp = F.formatter_of_out_channel oc_call_exp;
      libcall_exp = F.formatter_of_out_channel oc_libcall_exp;
      readcall_exp = F.formatter_of_out_channel oc_readcall_exp;
      real_lv = F.formatter_of_out_channel oc_real_lv;
      const_exp = F.formatter_of_out_channel oc_const;
      lval_exp = F.formatter_of_out_channel oc_lval;
      binop_exp = F.formatter_of_out_channel oc_binop_exp;
      unop_exp = F.formatter_of_out_channel oc_unop_exp;
      cast_exp = F.formatter_of_out_channel oc_cast;
      sizeof_exp = F.formatter_of_out_channel oc_sizeof;
      other_exp = F.formatter_of_out_channel oc_exp;
      global_var = F.formatter_of_out_channel oc_global_var;
      local_var = F.formatter_of_out_channel oc_local_var;
      field = F.formatter_of_out_channel oc_field;
      st_fld = F.formatter_of_out_channel oc_st_fld;
      index = F.formatter_of_out_channel oc_index;
      lval = F.formatter_of_out_channel oc_lv;
      mem = F.formatter_of_out_channel oc_mem;
      start_of = F.formatter_of_out_channel oc_start_of;
      addr_of = F.formatter_of_out_channel oc_addr_of;
      (* BinOp *)
      binop = F.formatter_of_out_channel oc_binop;
      plusa = F.formatter_of_out_channel oc_plusa;
      pluspi = F.formatter_of_out_channel oc_pluspi;
      indexpi = F.formatter_of_out_channel oc_indexpi;
      minusa = F.formatter_of_out_channel oc_minusa;
      minuspi = F.formatter_of_out_channel oc_minuspi;
      minuspp = F.formatter_of_out_channel oc_minuspp;
      mult = F.formatter_of_out_channel oc_mult;
      div = F.formatter_of_out_channel oc_div;
      modd = F.formatter_of_out_channel oc_modd;
      shiftlt = F.formatter_of_out_channel oc_shiftlt;
      shiftrt = F.formatter_of_out_channel oc_shiftrt;
      lt = F.formatter_of_out_channel oc_lt;
      gt = F.formatter_of_out_channel oc_gt;
      le = F.formatter_of_out_channel oc_le;
      ge = F.formatter_of_out_channel oc_ge;
      eq = F.formatter_of_out_channel oc_eq;
      ne = F.formatter_of_out_channel oc_ne;
      band = F.formatter_of_out_channel oc_band;
      bxor = F.formatter_of_out_channel oc_bxor;
      bor = F.formatter_of_out_channel oc_bor;
      landd = F.formatter_of_out_channel oc_landd;
      lorr = F.formatter_of_out_channel oc_lorr;
      (* UnOp *)
      unop = F.formatter_of_out_channel oc_unop;
      bnot = F.formatter_of_out_channel oc_bnot;
      lnot = F.formatter_of_out_channel oc_lnot;
      neg = F.formatter_of_out_channel oc_neg;
      (* Sems for Patron *)
      evallv = F.formatter_of_out_channel oc_evallv;
      allocpath = F.formatter_of_out_channel oc_allocpath;
      readpath = F.formatter_of_out_channel oc_readpath;
    }
  in
  let channels =
    [
      oc_func;
      oc_entry;
      oc_exit;
      oc_join;
      oc_skip;
      oc_assign;
      oc_assume;
      oc_alloc;
      oc_salloc;
      oc_call;
      oc_libcall;
      oc_arg;
      oc_return;
      oc_cmd;
      oc_set;
      oc_alloc_exp;
      oc_salloc_exp;
      oc_call_exp;
      oc_libcall_exp;
      oc_readcall_exp;
      oc_real_lv;
      oc_const;
      oc_lval;
      oc_binop_exp;
      oc_unop_exp;
      oc_cast;
      oc_sizeof;
      oc_exp;
      oc_global_var;
      oc_local_var;
      oc_field;
      oc_st_fld;
      oc_index;
      oc_lv;
      oc_mem;
      oc_start_of;
      oc_addr_of;
      oc_binop;
      oc_plusa;
      oc_pluspi;
      oc_indexpi;
      oc_minusa;
      oc_minuspi;
      oc_minuspp;
      oc_mult;
      oc_div;
      oc_modd;
      oc_shiftlt;
      oc_shiftrt;
      oc_lt;
      oc_gt;
      oc_le;
      oc_ge;
      oc_eq;
      oc_ne;
      oc_band;
      oc_bxor;
      oc_bor;
      oc_landd;
      oc_lorr;
      oc_unop;
      oc_bnot;
      oc_lnot;
      oc_neg;
      oc_evallv;
      oc_allocpath;
      oc_readpath;
    ]
  in
  (fmt, channels)

let close_formatters fmt channels =
  (* Function body *)
  F.pp_print_flush fmt.func ();
  (* Command *)
  F.pp_print_flush fmt.entry ();
  F.pp_print_flush fmt.exit ();
  F.pp_print_flush fmt.join ();
  F.pp_print_flush fmt.skip ();
  F.pp_print_flush fmt.assign ();
  F.pp_print_flush fmt.assume ();
  F.pp_print_flush fmt.alloc ();
  F.pp_print_flush fmt.salloc ();
  F.pp_print_flush fmt.call ();
  F.pp_print_flush fmt.libcall ();
  F.pp_print_flush fmt.arg ();
  F.pp_print_flush fmt.return ();
  F.pp_print_flush fmt.cmd ();
  (* Cmd for Patron *)
  F.pp_print_flush fmt.set ();
  F.pp_print_flush fmt.alloc_exp ();
  F.pp_print_flush fmt.salloc_exp ();
  F.pp_print_flush fmt.call_exp ();
  F.pp_print_flush fmt.libcall_exp ();
  F.pp_print_flush fmt.readcall_exp ();
  F.pp_print_flush fmt.real_lv ();
  (* Expressions *)
  F.pp_print_flush fmt.const_exp ();
  F.pp_print_flush fmt.lval_exp ();
  F.pp_print_flush fmt.binop_exp ();
  F.pp_print_flush fmt.unop_exp ();
  F.pp_print_flush fmt.cast_exp ();
  F.pp_print_flush fmt.sizeof_exp ();
  F.pp_print_flush fmt.other_exp ();
  F.pp_print_flush fmt.global_var ();
  F.pp_print_flush fmt.local_var ();
  F.pp_print_flush fmt.field ();
  F.pp_print_flush fmt.st_fld ();
  F.pp_print_flush fmt.index ();
  F.pp_print_flush fmt.lval ();
  F.pp_print_flush fmt.mem ();
  F.pp_print_flush fmt.start_of ();
  F.pp_print_flush fmt.addr_of ();
  (* BinOp *)
  F.pp_print_flush fmt.binop ();
  F.pp_print_flush fmt.plusa ();
  F.pp_print_flush fmt.pluspi ();
  F.pp_print_flush fmt.indexpi ();
  F.pp_print_flush fmt.minusa ();
  F.pp_print_flush fmt.minuspi ();
  F.pp_print_flush fmt.minuspp ();
  F.pp_print_flush fmt.mult ();
  F.pp_print_flush fmt.div ();
  F.pp_print_flush fmt.modd ();
  F.pp_print_flush fmt.shiftlt ();
  F.pp_print_flush fmt.shiftrt ();
  F.pp_print_flush fmt.lt ();
  F.pp_print_flush fmt.gt ();
  F.pp_print_flush fmt.le ();
  F.pp_print_flush fmt.ge ();
  F.pp_print_flush fmt.eq ();
  F.pp_print_flush fmt.ne ();
  F.pp_print_flush fmt.band ();
  F.pp_print_flush fmt.bxor ();
  F.pp_print_flush fmt.bor ();
  F.pp_print_flush fmt.landd ();
  F.pp_print_flush fmt.lorr ();
  (* UnOp *)
  F.pp_print_flush fmt.unop ();
  F.pp_print_flush fmt.bnot ();
  F.pp_print_flush fmt.lnot ();
  F.pp_print_flush fmt.neg ();
  (* Sems for Patron *)
  F.pp_print_flush fmt.evallv ();
  F.pp_print_flush fmt.allocpath ();
  F.pp_print_flush fmt.readpath ();
  List.iter close_out channels

let print_relation dirname icfg =
  let fmt, channels = make_formatters dirname in
  List.iter (fun n -> pp_cmd fmt icfg n) (InterCfg.nodesof icfg);
  close_formatters fmt channels

let rec string_of_abstract_exp = function
  | Cil.Const _ -> "C"
  | Cil.Lval (Cil.Var v, _) when v.vstorage = Cil.Extern -> v.vname
  | Cil.Lval _ | Cil.StartOf _ -> "X"
  | Cil.BinOp (bop, e1, e2, _) ->
      string_of_abstract_exp e1 ^ CilHelper.s_bop bop
      ^ string_of_abstract_exp e2
  | Cil.UnOp (uop, e, _) -> CilHelper.s_uop uop ^ string_of_abstract_exp e
  | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ -> "SizeOf"
  | Cil.CastE (_, e) -> string_of_abstract_exp e
  | Cil.AddrOf _ -> "&X"
  | _ -> ""

let print_raw dirname =
  let oc_exp_json = open_out (dirname ^ "/Exp.json") in
  let oc_exp_text = open_out (dirname ^ "/Exp.map") in
  let text_fmt = F.formatter_of_out_channel oc_exp_text in
  let l =
    Hashtbl.fold
      (fun exp id l ->
        F.fprintf text_fmt "%s\t%s\n" id (CilHelper.s_exp exp);
        let json_exp = CilJson.of_exp exp in
        let exp =
          `Assoc
            [
              ("tree", json_exp);
              ("text", `String (CilHelper.s_exp exp));
              ("abs_text", `String (string_of_abstract_exp exp));
            ]
        in
        (id, exp) :: l)
      exp_map []
  in
  let json = `Assoc l in
  Yojson.Safe.to_channel oc_exp_json json;
  close_out oc_exp_json;
  close_out oc_exp_text

let print analysis icfg =
  Hashtbl.reset exp_map;
  Hashtbl.reset lv_map;
  Hashtbl.reset binop_map;
  Hashtbl.reset unop_map;
  let dirname = FileManager.analysis_dir analysis ^ "/datalog" in
  print_relation dirname icfg;
  print_raw dirname
