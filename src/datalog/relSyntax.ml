open BasicDom
open Cil
open IntraCfg
open Cmd
open Vocab

module F = Format
module Node = InterCfg.Node

type formatter =
  { entry : F.formatter
  ; exit : F.formatter
  ; skip : F.formatter
  ; assign : F.formatter
  ; alloc : F.formatter
  ; call : F.formatter
  ; libcall : F.formatter
  ; arg : F.formatter
  ; return : F.formatter
  ; cmd : F.formatter
  (* expression *)
  ; const_exp : F.formatter
  ; lval_exp : F.formatter
  ; binop_exp : F.formatter
  ; cast_exp : F.formatter
  ; other_exp : F.formatter
  (* lv *)
  ; lval : F.formatter }

let exp_count = ref 0
let exp_map = Hashtbl.create 1000
let new_exp_id e =
  let id = "Exp-" ^ string_of_int !exp_count in
  exp_count := !exp_count + 1;
  Hashtbl.add exp_map e id;
  id

let lv_count = ref 0
let lv_map = Hashtbl.create 1000
let new_lv_id lv =
  let id = "Lval-" ^ string_of_int !lv_count in
  lv_count := !lv_count + 1;
  Hashtbl.add lv_map lv id;
  id

let rec pp_lv fmt lv =
  if Hashtbl.mem lv_map lv then ()
  else
    let id = new_lv_id lv in
    match lv with
    | Var vi, NoOffset ->
      F.fprintf fmt.lval "%s\t%s\n" id vi.vname
    | _, _ ->
      F.fprintf fmt.lval "%s\tOther\n" id

and pp_exp fmt e =
  if Hashtbl.mem exp_map e then ()
  else
    let id = new_exp_id e in
    match e with
    | Cil.Const _ -> F.fprintf fmt.const_exp "%s\n" id
    | Cil.Lval lv ->
      pp_lv fmt lv;
      let lv_id = Hashtbl.find lv_map lv in
      F.fprintf fmt.lval_exp "%s\t%s\n" id lv_id
    | Cil.BinOp (bop, e1, e2, _) ->
      pp_exp fmt e1;
      pp_exp fmt e2;
      let e1_id = Hashtbl.find exp_map e1 in
      let e2_id = Hashtbl.find exp_map e2 in
      F.fprintf fmt.binop_exp "%s\t%s\t%s\t%s\n"
        id (CilHelper.s_bop bop) e1_id e2_id
    | Cil.CastE (_, e1) ->
      pp_exp fmt e1;
      let e1_id = Hashtbl.find exp_map e1 in
      F.fprintf fmt.cast_exp "%s\t%s\n" id e1_id
    | _ -> F.fprintf fmt.other_exp "%s\n" id

let pp_cmd fmt icfg n =
  match InterCfg.cmdof icfg n with
  | Cskip _ ->
    if InterCfg.is_entry n then
      F.fprintf fmt.entry "%a\n" Node.pp n
    else if InterCfg.is_exit n then
      F.fprintf fmt.exit "%a\n" Node.pp n
    else
      F.fprintf fmt.skip "%a\n" Node.pp n
  | Cset (lv, e, _) ->
    pp_lv fmt lv;
    pp_exp fmt e;
    let lv_id = Hashtbl.find lv_map lv in
    let e_id = Hashtbl.find exp_map e in
    F.fprintf fmt.assign "%a\t%s\t%s\n" Node.pp n lv_id e_id
  | Cexternal (_,_) -> F.fprintf fmt.cmd "external\n"
  | Calloc (lv, Array e, _, _) ->
    pp_lv fmt lv;
    pp_exp fmt e;
    let lv_id = Hashtbl.find lv_map lv in
    let e_id = Hashtbl.find exp_map e in
    F.fprintf fmt.alloc "%a\t%s\t%s\n" Node.pp n lv_id e_id
  | Calloc (lv,_,_,_) -> F.fprintf fmt.cmd "alloc\n"
  | Csalloc (_, _, _) -> F.fprintf fmt.cmd "salloc\n"
  | Cfalloc (_, _, _) -> F.fprintf fmt.cmd "falloc\n"
  | Ccall (_, (Lval (Var f, NoOffset) as e), el, _)
    when f.vstorage = Cil.Extern ->
    pp_exp fmt e;
    let id = Hashtbl.find exp_map e in
    F.fprintf fmt.libcall "%a\t%s\n" Node.pp n id
  | Ccall (_, e, el, _) ->
    pp_exp fmt e;
    let id = Hashtbl.find exp_map e in
    F.fprintf fmt.call "%a\t%s\n" Node.pp n id
  | Creturn (Some e, _) ->
    pp_exp fmt e;
    let id = Hashtbl.find exp_map e in
    F.fprintf fmt.return "%a\t%s\n" Node.pp n id
  | Cassume (_,_) -> F.fprintf fmt.cmd "assume\n"
  | _ -> F.fprintf fmt.cmd "unknown"

let make_formatters dirname =
  let oc_const = open_out (dirname ^ "/ConstExp.facts") in
  let oc_lval = open_out (dirname ^ "/LvalExp.facts") in
  let oc_binop = open_out (dirname ^ "/BinOpExp.facts") in
  let oc_cast = open_out (dirname ^ "/CastExp.facts") in
  let oc_exp = open_out (dirname ^ "/OtherExp.facts") in
  let oc_cmd = open_out (dirname ^ "/Cmd.facts") in
  let oc_entry = open_out (dirname ^ "/Entry.facts") in
  let oc_exit = open_out (dirname ^ "/Exit.facts") in
  let oc_skip = open_out (dirname ^ "/Skip.facts") in
  let oc_assign = open_out (dirname ^ "/Assign.facts") in
  let oc_alloc = open_out (dirname ^ "/Alloc.facts") in
  let oc_libcall = open_out (dirname ^ "/LibCall.facts") in
  let oc_call = open_out (dirname ^ "/Call.facts") in
  let oc_arg = open_out (dirname ^ "/Arg.facts") in
  let oc_return = open_out (dirname ^ "/Return.facts") in
  let oc_lv = open_out (dirname ^ "/Lval.facts") in
  let fmt =
    { entry = F.formatter_of_out_channel oc_entry
    ; exit = F.formatter_of_out_channel oc_exit
    ; skip = F.formatter_of_out_channel oc_skip
    ; assign = F.formatter_of_out_channel oc_assign
    ; alloc = F.formatter_of_out_channel oc_alloc
    ; libcall = F.formatter_of_out_channel oc_libcall
    ; call = F.formatter_of_out_channel oc_call
    ; arg = F.formatter_of_out_channel oc_arg
    ; return = F.formatter_of_out_channel oc_return
    ; cmd = F.formatter_of_out_channel oc_cmd
    ; const_exp = F.formatter_of_out_channel oc_const
    ; lval_exp = F.formatter_of_out_channel oc_lval
    ; binop_exp = F.formatter_of_out_channel oc_binop
    ; cast_exp = F.formatter_of_out_channel oc_cast
    ; other_exp = F.formatter_of_out_channel oc_exp
    ; lval = F.formatter_of_out_channel oc_lv }
  in
  let channels =
    [ oc_const; oc_lval; oc_binop; oc_cast; oc_exp
    ; oc_cmd; oc_entry; oc_exit; oc_skip; oc_assign; oc_alloc; oc_call
    ; oc_libcall; oc_arg; oc_return; oc_lv ]
  in
  (fmt, channels)

let close_formatters fmt channels =
  F.pp_print_flush fmt.entry ();
  F.pp_print_flush fmt.exit ();
  F.pp_print_flush fmt.skip ();
  F.pp_print_flush fmt.assign ();
  F.pp_print_flush fmt.call ();
  F.pp_print_flush fmt.libcall ();
  F.pp_print_flush fmt.arg ();
  F.pp_print_flush fmt.return ();
  F.pp_print_flush fmt.cmd ();
  F.pp_print_flush fmt.const_exp ();
  F.pp_print_flush fmt.lval_exp ();
  F.pp_print_flush fmt.binop_exp ();
  F.pp_print_flush fmt.cast_exp ();
  F.pp_print_flush fmt.other_exp ();
  F.pp_print_flush fmt.lval ();
  List.iter close_out channels

let print_relation dirname icfg =
  let fmt, channels = make_formatters dirname in
  List.iter (fun n -> pp_cmd fmt icfg n) (InterCfg.nodesof icfg);
  close_formatters fmt channels

let rec string_of_abstract_exp = function
  | Cil.Const _ -> "C"
  | Cil.Lval (Cil.Var v, _) when v.vstorage = Cil.Extern -> v.vname
  | Cil.Lval _
  | Cil.StartOf _ -> "X"
  | Cil.BinOp (bop, e1, e2, _) ->
    string_of_abstract_exp e1 ^ CilHelper.s_bop bop ^ string_of_abstract_exp e2
  | Cil.UnOp (uop, e, _) ->
    CilHelper.s_uop uop ^ string_of_abstract_exp e
  | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ -> "SizeOf"
  | Cil.CastE (_, e) -> string_of_abstract_exp e
  | Cil.AddrOf _ -> "&X"
  | _ -> ""

let print_raw dirname =
  let oc_exp_json = open_out (dirname ^ "/Exp.json") in
  let oc_exp_text = open_out (dirname ^ "/Exp.map") in
  let text_fmt = F.formatter_of_out_channel oc_exp_text in
  let l = Hashtbl.fold (fun exp id l ->
      F.fprintf text_fmt "%s\t%s\n" id (CilHelper.s_exp exp);
      let json_exp = CilJson.of_exp exp in
      let exp = `Assoc [ ("tree", json_exp)
                       ; ("text", `String (CilHelper.s_exp exp))
                       ; ("abs_text", `String (string_of_abstract_exp exp)) ]
      in
      (id, exp)::l
    ) exp_map []
  in
  let json = `Assoc l in
  Yojson.Safe.to_channel oc_exp_json json;
  close_out oc_exp_json;
  close_out oc_exp_text

let print icfg =
  let dirname = !Options.outdir ^ "/datalog" in
  print_relation dirname icfg;
  print_raw dirname
