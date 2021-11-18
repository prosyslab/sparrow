open Vocab
module H = Hashtbl
module C = Clang
module F = Format
module L = Logging

exception UnknownSyntax

type tmp_var_info = {
  tmp_var_lval : Cil.lval;
  tmp_var_expr : Cil.exp;
  tmp_var_stmt : Cil.stmt;
  unary_plus_expr : Cil.exp;
}

type flags = {
  mutable tmp_var_cond_update : int;
  mutable skip_while : bool;
  mutable while_flag : bool;
  mutable total_initialized_items_len : int;
  mutable terminate_flag : bool;
}

module EnvData = struct
  type t = EnvVar of Cil.varinfo | EnvEnum of Cil.exp | EnvTyp of Cil.typ

  let to_string = function
    | EnvVar vi -> vi.vname
    | EnvEnum e -> CilHelper.s_exp e
    | EnvTyp t -> CilHelper.s_type t
end

module BlockEnv = struct
  module H = Map.Make (String)

  type t = {
    mutable var : EnvData.t H.t;
    mutable typ : Cil.typ H.t;
    mutable comp : Cil.typ H.t;
  }

  let create () = { var = H.empty; typ = H.empty; comp = H.empty }

  let add_var name vi env =
    env.var <- H.add name vi env.var;
    env

  let add_typ name typ env =
    env.typ <- H.add name typ env.typ;
    env

  let add_comp name comp env =
    env.comp <- H.add name comp env.comp;
    env

  let mem_var name env = H.mem name env.var

  let mem_typ name env = H.mem name env.typ

  let mem_comp name env = H.mem name env.comp

  let find_var name env = H.find name env.var

  let find_typ name env = H.find name env.typ

  let find_comp name env = H.find name env.comp
end

module LabelEnv = struct
  type t = { label : (string, string) H.t }

  let create () = { label = H.create 64 }

  let add_label name env =
    H.add env.label name name;
    env

  let mem_label name env = H.mem env.label name

  let find_label name env = H.find env.label name
end

module Scope = struct
  type t = BlockEnv.t list * LabelEnv.t list (* (BlockScope * FunScope) List *)

  let empty = ([], [])

  let create () = ([ BlockEnv.create () ], [ LabelEnv.create () ])

  let enter_block scope =
    match scope with bs, fs -> (BlockEnv.create () :: bs, fs)

  let enter_function scope =
    match scope with
    | bs, fs -> (BlockEnv.create () :: bs, LabelEnv.create () :: fs)

  (* exit_block is never needed, since scope is immutable *)
  let exit_function scope = match scope with bs, fs -> (List.tl bs, List.tl fs)

  let add name varinfo = function
    | (h :: _, _) as l ->
        ignore (BlockEnv.add_var name varinfo h);
        l
    | [], _ -> failwith "empty block scope"

  let add_type name typ = function
    | (h :: _, _) as l ->
        ignore (BlockEnv.add_typ name typ h);
        l
    | [], _ -> failwith "empty block scope"

  let add_comp name comp = function
    | (h :: _, _) as l ->
        ignore (BlockEnv.add_comp name comp h);
        l
    | [], _ -> failwith "empty block scope"

  let add_label name = function
    | (_, h :: _) as l ->
        ignore (LabelEnv.add_label name h);
        l
    | _, [] -> failwith "empty function scope"

  let rec mem_var name = function
    | h :: t, fs ->
        if BlockEnv.mem_var name h then true else mem_var name (t, fs)
    | [], _ -> false

  let rec mem_typ name = function
    | h :: t, fs ->
        if BlockEnv.mem_typ name h then true else mem_typ name (t, fs)
    | [], _ -> false

  let rec mem_comp name = function
    | h :: t, fs ->
        if BlockEnv.mem_comp name h then true else mem_comp name (t, fs)
    | [], _ -> false

  let rec mem_label name = function
    | bs, h :: t ->
        if LabelEnv.mem_label name h then true else mem_label name (bs, t)
    | _, [] -> false

  let rec find_var_enum ?(allow_undef = false) name = function
    | h :: t, fs -> (
        try BlockEnv.find_var name h
        with Not_found -> find_var_enum ~allow_undef name (t, fs))
    | [], _ when allow_undef ->
        let ftype = Cil.TFun (Cil.intType, None, false, []) in
        EnvData.EnvVar (Cil.makeGlobalVar name ftype)
    | _ -> failwith ("variable " ^ name ^ " not found")

  let rec find_type name = function
    | h :: t, fs -> (
        try BlockEnv.find_typ name h with Not_found -> find_type name (t, fs))
    | [], _ when name = "__builtin_va_list" || name = "__va_list_tag" ->
        Cil.TBuiltin_va_list []
    | [], _ when name = "__int128_t" -> Cil.TInt (Cil.ILongLong, [])
    | [], _ when name = "__uint128_t" -> Cil.TInt (Cil.IULongLong, [])
    | _ -> failwith ("type of " ^ name ^ " not found")

  let rec find_comp ?(compinfo = None) name = function
    | h :: t, fs -> (
        try BlockEnv.find_comp name h
        with Not_found -> find_comp ~compinfo name (t, fs))
    | [], _ when compinfo <> None ->
        let compinfo = Option.get compinfo in
        if compinfo.Cil.cname = name then Cil.TComp (compinfo, [])
        else failwith ("comp type of " ^ name ^ " not found (case 1)")
    | _ -> failwith ("comp type of " ^ name ^ " not found (case 2)")

  let pp fmt scope =
    List.iter
      (fun env ->
        F.fprintf fmt "=====\n";
        H.iter
          (fun name v -> F.fprintf fmt "%s -> %s\n" name (EnvData.to_string v))
          env;
        F.fprintf fmt "=====\n")
      scope
end

let empty_block = { Cil.battrs = []; bstmts = [] }

let struct_id_count = ref 0

let is_init_list (expr : C.Ast.expr) =
  match expr.C.Ast.desc with C.Ast.InitList _ -> true | _ -> false

let anonymous_id_table = H.create 1024

let new_record_id is_struct (rdecl : C.Ast.record_decl) cursor =
  if rdecl.C.Ast.name = "" then (
    let h = C.hash_cursor cursor in
    if H.mem anonymous_id_table h then (H.find anonymous_id_table h, false)
    else
      let kind = if is_struct then "struct" else "union" in
      let name = "__anon" ^ kind ^ "_" ^ string_of_int !struct_id_count in
      struct_id_count := !struct_id_count + 1;
      H.add anonymous_id_table h name;
      (name, true))
  else (rdecl.name, false)

let new_enum_id name =
  let new_id = "__anonenum_" ^ name ^ "_" ^ string_of_int !struct_id_count in
  struct_id_count := !struct_id_count + 1;
  new_id

type exp_action = ADrop | AExp

let alpha_count = ref 0

let create_new_global_variable scope name typ =
  let new_name =
    if Scope.mem_var name scope then (
      let new_name = name ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name)
    else name
  in
  let varinfo = Cil.makeGlobalVar new_name typ in
  let scope = Scope.add name (EnvData.EnvVar varinfo) scope in
  (varinfo, scope)

let find_global_variable scope name typ =
  if Scope.mem_var name scope then
    let envdata = Scope.find_var_enum name scope in
    match envdata with
    | EnvData.EnvVar vi -> (vi, scope)
    | _ -> create_new_global_variable scope name typ
  else create_new_global_variable scope name typ

let create_local_variable scope fundec name typ =
  let new_name =
    if Scope.mem_var name scope then (
      let new_name = name ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name)
    else name
  in
  let varinfo = Cil.makeLocalVar fundec new_name typ in
  let scope = Scope.add name (EnvData.EnvVar varinfo) scope in
  (varinfo, scope)

let create_label scope label =
  let new_name =
    if Scope.mem_label label scope then (
      let new_name = label ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name)
    else label
  in
  let scope = Scope.add_label new_name scope in
  (new_name, scope)

let trans_location node =
  let location =
    C.Ast.location_of_node node |> C.Ast.concrete_of_source_location C.Presumed
  in
  { Cil.file = location.filename; line = location.line; byte = location.column }

let get_compinfo typ =
  match Cil.unrollType typ with
  | Cil.TComp (ci, _) -> ci
  | _ -> failwith ("invalid type: " ^ CilHelper.s_type typ)

let trans_int_kind : C.Ast.builtin_type -> Cil.ikind = function
  | C.Int | C.Bool -> Cil.IInt
  | C.Char_U | C.UChar -> Cil.IUChar
  | C.UShort -> Cil.IUShort
  | C.UInt -> Cil.IUInt
  | C.ULong -> Cil.IULong
  | C.ULongLong -> Cil.IULongLong
  | C.Char_S -> Cil.IChar
  | C.SChar -> Cil.ISChar
  | C.Short -> Cil.IShort
  | C.Long -> Cil.ILong
  | C.LongLong -> Cil.ILongLong
  | _ -> invalid_arg "int kind"

let trans_float_kind : C.Ast.builtin_type -> Cil.fkind = function
  | C.Float -> Cil.FFloat
  | C.Double -> Cil.FDouble
  | C.LongDouble -> Cil.FLongDouble
  | _ -> invalid_arg "float kind"

let trans_binop lhs rhs = function
  | C.Mul -> Cil.Mult
  | C.Div -> Cil.Div
  | C.Rem -> Cil.Mod
  | C.Add when Cil.typeOf lhs |> Cil.isPointerType -> Cil.PlusPI
  | C.Add -> Cil.PlusA
  | C.Sub
    when Cil.typeOf lhs |> Cil.isPointerType
         && Cil.typeOf rhs |> Cil.isPointerType ->
      Cil.MinusPP
  | C.Sub when Cil.typeOf lhs |> Cil.isPointerType -> Cil.MinusPI
  | C.Sub -> Cil.MinusA
  | C.Shl -> Cil.Shiftlt
  | C.Shr -> Cil.Shiftrt
  | C.LT -> Cil.Lt
  | C.GT -> Cil.Gt
  | C.LE -> Cil.Le
  | C.GE -> Cil.Ge
  | C.EQ -> Cil.Eq
  | C.NE -> Cil.Ne
  | C.And -> Cil.BAnd
  | C.Xor -> Cil.BXor
  | C.Or -> Cil.BOr
  | C.LAnd -> Cil.LAnd
  | C.LOr -> Cil.LOr
  | _ -> failwith "invalid binop"

let string_of_declaration_name name =
  match name with
  | C.Ast.IdentifierName s -> s
  | _ -> failwith "name_of_ident_ref"

let name_of_ident_ref idref = string_of_declaration_name idref.C.Ast.name

let const_attribute = [ Cil.Attr ("const", []) ]

let trans_attribute typ = if typ.C.Ast.const then const_attribute else []

let failwith_decl (decl : C.Ast.decl) =
  match decl.C.Ast.desc with
  | C.Ast.RecordDecl _ -> failwith "record decl"
  | _ -> failwith "unknown decl"

let trans_integer_literal decoration il =
  let ikind =
    match decoration with
    | C.Ast.Cursor c -> C.get_cursor_type c |> C.get_type_kind |> trans_int_kind
    | _ -> failwith "Invalid cursor for integer literal"
  in
  match il with
  | C.Ast.Int i -> Cil.kinteger ikind i
  | C.Ast.CXInt cxi ->
      Cil.kinteger ikind (Clang__.Clang__bindings.ext_int_get_sext_value cxi)

let trans_floating_literal decoration il =
  let fkind =
    match decoration with
    | C.Ast.Cursor c ->
        C.get_cursor_type c |> C.get_type_kind |> trans_float_kind
    | _ -> failwith "Invalid cursor for float literal"
  in
  match il with
  | C.Ast.Float f -> Cil.Const (Cil.CReal (f, fkind, None))
  | C.Ast.CXFloat cxf ->
      let f =
        match fkind with
        | Cil.FFloat -> Clang__.Clang__bindings.ext_float_convert_to_float cxf
        | Cil.FDouble | Cil.FLongDouble ->
            Clang__.Clang__bindings.ext_float_convert_to_double cxf
      in
      Cil.Const (Cil.CReal (f, fkind, None))

let trans_string_literal sl = Cil.Const (Cil.CStr sl.C.Ast.bytes)

let type_of_decoration decoration =
  match decoration with
  | C.Ast.Cursor c -> C.get_cursor_type c
  | _ -> failwith "Invalid cursor for type"

let trans_decl_ref scope allow_undef idref =
  let name = name_of_ident_ref idref in
  match Scope.find_var_enum ~allow_undef name scope with
  | EnvVar varinfo ->
      let exp = Cil.Lval (Cil.Var varinfo, NoOffset) in
      ([], Some exp)
  | EnvEnum enum -> ([], Some enum)
  | _ -> failwith "no found"

let grab_matching_field cfields f (expr : C.Ast.expr) =
  List.fold_left
    (fun (fi', find, idx) fi ->
      let fi'', find, idx =
        match expr.C.Ast.desc with
        | C.Ast.DesignatedInit d ->
            List.fold_left
              (fun (fi', find, idx) designator ->
                match designator with
                | C.Ast.FieldDesignator f ->
                    if f = fi.Cil.fname then ([ fi ], idx, idx)
                    else (fi', find, idx)
                | C.Ast.ArrayDesignator _ -> (fi', find, idx)
                | C.Ast.ArrayRangeDesignator (_, _) -> (fi', find, idx))
              (fi', find, idx) d.designators
        | _ -> if fi' <> [] then (fi', find, idx) else ([ f ], find, -10000)
      in
      (fi'', find, idx + 1))
    ([], 0, 0) cfields

let sort_list_with_index data_list idx_list =
  List.combine data_list idx_list
  |> List.sort (fun (_, idx1) (_, idx2) -> if idx1 > idx2 then 1 else 0)
  |> List.split |> fst |> List.rev

let should_ignore_implicit_cast expr qual_type e typ =
  (* heuristics to selectively make implicit cast explicit because clangml
   * does not fully expose all the implicit casting information *)
  if
    Cil.unrollType typ |> Cil.isPointerType
    && Cil.typeOf e |> Cil.unrollType |> Cil.isIntegralType
  then false
  else
    let expr_kind = C.Ast.cursor_of_node expr |> C.ext_get_cursor_kind in
    let type_kind =
      C.get_pointee_type qual_type.C.Ast.cxtype |> C.ext_type_get_kind
    in
    (* ignore FunctionToPointerDecay and BuiltinFnToFnPtr *)
    expr_kind = C.ImplicitCastExpr
    && (type_kind = C.FunctionNoProto || type_kind = C.FunctionProto)
    (* ignore LValueToRValue *)
    || CilHelper.eq_typ (Cil.typeOf e) typ

let rec append_instr_internal sl instr result =
  match sl with
  | [ ({ Cil.skind = Cil.Instr l; _ } as h) ] ->
      h.skind <- Cil.Instr (l @ [ instr ]);
      h :: result
  | [] -> Cil.mkStmt (Cil.Instr [ instr ]) :: result
  | h :: t -> append_instr_internal t instr (h :: result)

let append_instr sl instr = append_instr_internal sl instr [] |> List.rev

let rec append_stmt_list_internal sl1 sl2 result =
  match (sl1, sl2) with
  | ( [ ({ Cil.skind = Cil.Instr l1; _ } as h1) ],
      ({ Cil.skind = Cil.Instr l2; _ } as h2) :: t2 )
  (* merging statements with labels may break goto targets *)
    when h1.labels = [] && h2.labels = [] ->
      List.rev_append ({ h1 with skind = Cil.Instr (l1 @ l2) } :: t2) result
  | [], _ -> List.rev_append sl2 result
  | h1 :: t1, _ -> append_stmt_list_internal t1 sl2 (h1 :: result)

let append_stmt_list sl1 sl2 = append_stmt_list_internal sl1 sl2 [] |> List.rev

let rec trans_type ?(compinfo = None) scope (typ : C.Type.t) =
  match typ.C.Ast.desc with
  | Pointer pt -> (
      try Cil.TPtr (trans_type ~compinfo scope pt, trans_attribute typ)
      with _ ->
        (* TODO: https://github.com/prosyslab/sparrow/issues/28 *)
        L.warn ~to_consol:false "WARN: type not found\n";
        Cil.voidPtrType)
  | FunctionType ft -> trans_function_type scope None ft |> fst
  | Typedef td -> Scope.find_type (name_of_ident_ref td) scope
  | Elaborated et -> trans_type ~compinfo scope et.named_type
  | Record rt ->
      let name = name_of_ident_ref rt in
      let name, scope =
        if name = "" then
          let decl = C.Type.get_declaration typ in
          let rdecl, is_struct =
            match decl.C.Ast.desc with
            | C.Ast.RecordDecl rdecl -> (rdecl, rdecl.C.Ast.keyword = C.Struct)
            | _ -> failwith "Invalid type"
          in
          let cursor = C.Ast.cursor_of_decoration decl.decoration in
          let name, is_new_anon = new_record_id is_struct rdecl cursor in
          let callback compinfo =
            List.fold_left
              (fun fl (decl : C.Ast.decl) ->
                match decl.C.Ast.desc with
                | C.Ast.Field _ -> fl @ [ trans_field_decl scope compinfo decl ]
                | C.Ast.IndirectField _ ->
                    fl @ trans_indirect_field_decl scope compinfo decl
                | _ -> fl)
              [] rdecl.fields
          in
          let scope =
            if is_new_anon then
              let compinfo = Cil.mkCompInfo is_struct name callback [] in
              let tcomp = Cil.TComp (compinfo, []) in
              Scope.add_comp name tcomp scope
            else scope
          in
          (name, scope)
        else (name, scope)
      in
      Scope.find_comp ~compinfo name scope
  | Enum et -> Scope.find_type (name_of_ident_ref et) scope
  | InvalidType ->
      L.warn ~to_consol:false "WARN: invalid type (use int instead)\n";
      Cil.intType
  | Vector vt ->
      let size = Cil.integer vt.size in
      let elem_type = trans_type ~compinfo scope vt.element in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, Some size, attr)
  | BuiltinType _ -> trans_builtin_type ~compinfo scope typ
  | ConstantArray ca ->
      let size = Cil.integer ca.size in
      let elem_type = trans_type ~compinfo scope ca.element in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, Some size, attr)
  | IncompleteArray ia_type ->
      let elem_type = trans_type ~compinfo scope ia_type in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, None, attr)
  | VariableArray va ->
      let _, size = trans_expr scope None Cil.locUnknown AExp va.size in
      let elem_type = trans_type ~compinfo scope va.element in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, Some (Option.get size), attr)
  | _ -> trans_builtin_type ~compinfo scope typ

and trans_builtin_type ?(compinfo = None) scope t =
  let k = C.get_type_kind t.C.Ast.cxtype in
  let attr = trans_attribute t in
  match k with
  | C.Void -> Cil.TVoid attr
  (* integer types *)
  | C.Int | C.Bool | C.Char_U | C.UChar | C.UShort | C.UInt | C.ULong
  | C.ULongLong | C.Char_S | C.SChar | C.Short | C.Long | C.LongLong ->
      Cil.TInt (trans_int_kind (k : C.Ast.builtin_type), attr)
  | C.Float | C.Double | C.LongDouble -> Cil.TFloat (trans_float_kind k, attr)
  | C.Pointer -> failwith "pointer"
  | C.Enum -> failwith "enum"
  | C.Typedef -> failwith "typedef"
  | C.FunctionNoProto -> failwith "typedef"
  | C.FunctionProto -> failwith "typedef"
  | C.ConstantArray ->
      let size = C.get_array_size t.cxtype |> Cil.integer in
      let elem_type =
        C.get_array_element_type t.cxtype
        |> C.Type.of_cxtype |> trans_type ~compinfo scope
      in
      Cil.TArray (elem_type, Some size, attr)
  | C.VariableArray | C.IncompleteArray ->
      let elem_type =
        C.get_array_element_type t.cxtype
        |> C.Type.of_cxtype |> trans_type ~compinfo scope
      in
      Cil.TArray (elem_type, None, attr)
  | Unexposed ->
      let canonical_typ = C.get_canonical_type t.cxtype in
      let canonical_typ_kind = canonical_typ |> C.get_type_kind in
      if canonical_typ_kind = C.Unexposed then (
        L.warn ~to_consol:false
          "WARN: Found Unexposed type recursively: translating to int\n";
        Cil.TInt (trans_int_kind k, attr))
      else canonical_typ |> C.Type.of_cxtype |> trans_type ~compinfo scope
  | Invalid -> failwith "type Invalid"
  | Char16 -> failwith "type Char16"
  | Char32 -> failwith "type Char32"
  | UInt128 | WChar | Int128 | NullPtr | Overload | Dependent | ObjCId ->
      failwith "9"
  | ObjCClass -> failwith "objc class"
  | ObjCSel -> failwith "objc sel"
  | Float128 -> failwith "float 128"
  | Half -> failwith "half"
  | Float16 -> failwith "float 16"
  | Complex | BlockPointer | LValueReference | RValueReference | Record ->
      failwith "7"
  | ObjCInterface | ObjCObjectPointer | Vector -> failwith ""
  | DependentSizedArray -> failwith "dependent"
  | MemberPointer -> failwith "6"
  | Auto | Elaborated | Pipe -> failwith "5"
  | _ ->
      F.fprintf F.err_formatter "%s" (C.get_type_spelling t.cxtype);
      F.fprintf F.err_formatter "\n";
      F.pp_print_flush F.err_formatter ();
      failwith "trans_builtin_type"

and trans_function_type scope fundec_opt typ =
  let return_typ = trans_type scope typ.C.Ast.result in
  let param_types, var_arg, scope =
    trans_parameter_types scope fundec_opt typ.C.Ast.parameters
  in
  (Cil.TFun (return_typ, param_types, var_arg, []), scope)

and trans_parameter_types scope fundec_opt = function
  | Some params ->
      let scope, formals =
        List.fold_left
          (fun (scope, formals) (param : C.Ast.parameter) ->
            let param_typ = trans_type scope param.desc.qual_type in
            let result = (param.desc.name, param_typ, []) in
            if param.desc.name = "" then (scope, result :: formals)
            else
              let make_var =
                match fundec_opt with
                | Some fundec -> fun n t -> Cil.makeFormalVar fundec n t
                | None -> fun n t -> Cil.makeVarinfo false n t
              in
              let vi = make_var param.desc.name param_typ in
              let scope = Scope.add param.desc.name (EnvData.EnvVar vi) scope in
              (scope, result :: formals))
          (scope, []) params.C.Ast.non_variadic
      in
      (List.rev formals |> Option.some, params.C.Ast.variadic, scope)
  | None -> (None, false, scope)

and trans_field_decl scope compinfo (field : C.Ast.decl) =
  let floc = trans_location field in
  match field.C.Ast.desc with
  | C.Ast.Field fdecl ->
      let typ = trans_type ~compinfo:(Some compinfo) scope fdecl.qual_type in
      (fdecl.name, typ, None, [], floc)
  | _ -> failwith_decl field

and trans_indirect_field_decl scope compinfo (ifdecl : C.Ast.decl) =
  match ifdecl.C.Ast.desc with
  | C.Ast.IndirectField fdecls ->
      (* IndirectField consists of several FieldDecls.
         Some of them are anonymous field whose name is '',
         and the rest are named fields.
         Only named fields are required to be embedded.*)
      let named_decls =
        List.fold_left
          (fun ndecls (fdecl : C.Ast.decl) ->
            match fdecl.C.Ast.desc with
            | C.Ast.Field fdecl_desc ->
                if fdecl_desc.name <> "" then fdecl :: ndecls else ndecls
            | _ -> failwith_decl fdecl)
          [] fdecls
      in

      List.fold_left
        (fun res ndecl -> res @ [ trans_field_decl scope compinfo ndecl ])
        [] named_decls
  | _ -> failwith_decl ifdecl

and trans_params scope args fundec =
  match args with
  | Some l ->
      List.fold_left
        (fun scope (param : C.Ast.parameter) ->
          let vi =
            Cil.makeFormalVar fundec param.desc.name
              (trans_type scope param.desc.qual_type)
          in
          Scope.add param.desc.name (EnvData.EnvVar vi) scope)
        scope l.C.Ast.non_variadic
  | None -> scope

(* In case of failure, produce 0 if default_ptr is false, a temp var if true *)
and trans_expr ?(allow_undef = false) ?(skip_lhs = false) ?(default_ptr = false)
    scope fundec_opt loc action (expr : C.Ast.expr) =
  match expr.C.Ast.desc with
  | C.Ast.IntegerLiteral il ->
      ([], Some (trans_integer_literal expr.decoration il))
  | C.Ast.FloatingLiteral fl ->
      ([], Some (trans_floating_literal expr.decoration fl))
  | C.Ast.StringLiteral sl -> ([], Some (trans_string_literal sl))
  | C.Ast.CharacterLiteral cl ->
      if cl.value > 255 then ([], Some (Cil.kinteger Cil.IUInt cl.value))
      else ([], Some (Cil.Const (Cil.CChr (char_of_int cl.value))))
  | C.Ast.UnaryOperator uo ->
      trans_unary_operator scope fundec_opt loc action uo.kind uo.operand
  | C.Ast.BinaryOperator bo ->
      trans_binary_operator scope fundec_opt loc bo.kind bo.lhs bo.rhs
  | C.Ast.DeclRef idref -> trans_decl_ref scope allow_undef idref
  | C.Ast.Call call ->
      trans_call scope skip_lhs fundec_opt loc call.callee call.args
  | C.Ast.Cast cast ->
      let typ = trans_type scope cast.qual_type in
      let is_void = match typ with Cil.TVoid _ -> true | _ -> false in
      let sl, expr_opt =
        (* skip_lhs is true if casting to void i.e. don't mind the variable or return value *)
        trans_expr ~allow_undef ~skip_lhs:is_void scope fundec_opt loc action
          cast.operand
      in
      if is_void then (sl, None)
      else
        let e = Option.get expr_opt in
        if should_ignore_implicit_cast expr cast.qual_type e typ then
          (sl, Some e)
        else (sl, Some (Cil.CastE (typ, e)))
  | C.Ast.Member mem ->
      ([], Some (trans_member scope fundec_opt loc mem.base mem.arrow mem.field))
  | C.Ast.ArraySubscript arr -> (
      let sl1, base = trans_expr scope fundec_opt loc action arr.base in
      let sl2, idx = trans_expr scope fundec_opt loc action arr.index in
      let base = Option.get base in
      (* base may contain casting such as (char * ) 0. But we have to preserve such important castings. Otherwise, CIL will crash  *)
      match CilHelper.remove_cast base with
      | Cil.Lval base' ->
          let new_lval =
            match idx with
            | Some x when Cil.isPointerType (Cil.typeOfLval base') ->
                ( Cil.Mem (Cil.BinOp (Cil.PlusPI, base, x, Cil.typeOf base)),
                  Cil.NoOffset )
            | Some x -> Cil.addOffsetLval (Cil.Index (x, Cil.NoOffset)) base'
            | _ -> failwith "lval"
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval))
      | Cil.BinOp (_, _, _, Cil.TArray (t, _, _)) ->
          let new_lval =
            match idx with
            | Some x ->
                ( Cil.Mem (Cil.BinOp (Cil.PlusPI, base, x, Cil.TPtr (t, []))),
                  Cil.NoOffset )
            | _ -> failwith "lval"
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval))
      | _ ->
          let new_lval =
            match idx with
            | Some x ->
                ( Cil.Mem (Cil.BinOp (Cil.PlusPI, base, x, Cil.typeOf base)),
                  Cil.NoOffset )
            | _ -> failwith "lval"
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval)))
  | C.Ast.ConditionalOperator co ->
      trans_cond_op scope fundec_opt loc co.cond co.then_branch co.else_branch
  | C.Ast.UnaryExpr ue ->
      trans_unary_expr scope fundec_opt loc ue.kind ue.argument
  | C.Ast.UnexposedExpr _ ->
      L.warn ~to_consol:false "UnexposedExpr at %s\n" (CilHelper.s_location loc);
      if default_ptr then
        match fundec_opt with
        | Some fundec ->
            let temp =
              (Cil.Var (Cil.makeTempVar fundec Cil.intPtrType), Cil.NoOffset)
            in
            ([], Some (Cil.Lval temp))
        | None -> ([], Some Cil.zero)
      else ([], Some Cil.zero)
  | C.Ast.InitList _ ->
      (* TODO: https://github.com/prosyslab/sparrow/issues/27 *)
      L.warn "Warning: init list @ %s\n" (CilHelper.s_location loc);
      ([], Some Cil.zero)
  | C.Ast.ImaginaryLiteral _ -> failwith "Unsupported syntax (ImaginaryLiteral)"
  | C.Ast.BoolLiteral _ -> failwith "Unsupported syntax (BoolLiteral)"
  | C.Ast.NullPtrLiteral -> failwith "Unsupported syntax (NullPtrLiteral)"
  | C.Ast.UnknownExpr (C.StmtExpr, C.StmtExpr) ->
      (* StmtExpr is not supported yet *)
      L.warn ~to_consol:false "StmtExpr at %s\n" (CilHelper.s_location loc);
      ([], Some Cil.zero)
  | C.Ast.DesignatedInit d -> trans_expr scope fundec_opt loc action d.init
  | C.Ast.UnknownExpr (_, _) ->
      print_endline "UnknownExpr not supported yet";
      L.warn ~to_consol:false "Unknown ext StmtExpr at %s\n"
        (CilHelper.s_location loc);
      ([], Some Cil.zero)
  | C.Ast.Predefined pre ->
      let cstr = Cil.CStr pre.function_name in
      let const = Cil.Const cstr in
      ([], Some const)
  | _ ->
      L.warn ~to_consol:false "Unknown at %s\n" (CilHelper.s_location loc);
      failwith "unknown trans_expr"

and trans_unary_operator scope fundec_opt loc action kind expr =
  let get_var var_opt =
    match var_opt with
    | Some x -> x
    | None ->
        prerr_endline (CilHelper.s_location loc);
        failwith "var_opt"
  in
  let lval_of_expr var =
    match var with Cil.Lval x -> x | x -> failwith (CilHelper.s_exp x)
  in
  match kind with
  | C.PostInc ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.PlusPI else Cil.PlusA
      in
      let fundec = Option.get fundec_opt in
      (* i++ ==> temp = i; i = i + 1; temp *)
      let typ = Cil.typeOf var in
      let temp = (Cil.Var (Cil.makeTempVar fundec typ), Cil.NoOffset) in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr2 = Cil.Set (lval_of_expr var, exp, loc) in
      if action = ADrop then
        (sl @ [ Cil.mkStmt (Cil.Instr [ instr2 ]) ], Some var)
      else
        let instr1 = Cil.Set (temp, var, loc) in
        ( sl @ [ Cil.mkStmt (Cil.Instr [ instr1; instr2 ]) ],
          Some (Cil.Lval temp) )
  | C.PostDec ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.MinusPI else Cil.MinusA
      in
      let fundec = Option.get fundec_opt in
      let typ = Cil.typeOf var in
      let temp = (Cil.Var (Cil.makeTempVar fundec typ), Cil.NoOffset) in
      let instr1 = Cil.Set (temp, var, loc) in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr2 = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr1; instr2 ]) ], Some (Cil.Lval temp))
  | C.PreInc ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.PlusPI else Cil.PlusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], Some var)
  | C.PreDec ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.MinusPI else Cil.MinusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], Some var)
  | C.AddrOf ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      (sl, Some (Cil.AddrOf (lval_of_expr var)))
  | C.Deref ->
      let sl, var_opt =
        trans_expr ~default_ptr:true scope fundec_opt loc action expr
      in
      let var = get_var var_opt in
      if Cil.typeOf var |> Cil.isArrayType then
        match CilHelper.remove_cast var with
        | Cil.Lval base ->
            ( sl,
              Some
                (Cil.Lval
                   (Cil.addOffsetLval (Cil.Index (Cil.zero, Cil.NoOffset)) base))
            )
        | Cil.BinOp (bop, e1, e2, Cil.TArray (t, _, _)) ->
            ( sl,
              Some
                (Cil.Lval
                   ( Cil.Mem (Cil.BinOp (bop, e1, e2, Cil.TPtr (t, []))),
                     Cil.NoOffset )) )
        | _ -> (sl, Some (Cil.Lval (Cil.Mem var, Cil.NoOffset)))
      else (sl, Some (Cil.Lval (Cil.Mem var, Cil.NoOffset)))
  | C.Plus ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      (sl, Some var)
  | C.Minus ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.Neg, var, typ)))
  | C.Not ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.BNot, var, typ)))
  | C.LNot ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.LNot, var, typ)))
  | C.Extension ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      (sl, Some var)
  | _ -> failwith ("unary_operator at " ^ CilHelper.s_location loc)

and trans_binary_operator scope fundec_opt loc kind lhs rhs =
  let lhs_sl, lhs_opt = trans_expr scope fundec_opt loc AExp lhs in
  let rhs_sl, rhs_opt = trans_expr scope fundec_opt loc AExp rhs in
  let lhs_expr =
    match lhs_opt with
    | Some x -> x
    | None ->
        L.warn ~to_consol:false "Invalid lhs at %s\n" (CilHelper.s_location loc);
        Cil.zero
  in
  let rhs_expr =
    match rhs_opt with
    | Some x -> x
    | None ->
        L.warn ~to_consol:false "Invalid rhs at %s\n" (CilHelper.s_location loc);
        Cil.zero
  in
  match kind with
  | C.Mul | C.Div | C.Rem | C.Add | C.Sub | C.Shl | C.Shr | C.LT | C.GT | C.LE
  | C.GE | C.EQ | C.NE | C.And | C.Xor | C.Or | C.LAnd | C.LOr ->
      let typ =
        if
          Cil.typeOf lhs_expr |> Cil.isIntegralType
          && Cil.typeOf rhs_expr |> Cil.isPointerType
        then Cil.typeOf rhs_expr
        else Cil.typeOf lhs_expr
      in
      ( rhs_sl @ lhs_sl,
        Cil.constFoldBinOp false
          (trans_binop lhs_expr rhs_expr kind)
          lhs_expr rhs_expr typ
        |> Option.some )
  | C.Assign -> (
      let lval =
        match lhs_expr with Cil.Lval l -> l | _ -> failwith "invalid lhs"
      in
      match (rhs_expr, rhs_sl) with
      | ( Cil.Lval _,
          [
            ({ Cil.skind = Cil.Instr [ Cil.Call (Some _, f, el, loc) ]; _ } as
            s);
          ] ) ->
          let stmt =
            { s with skind = Cil.Instr [ Cil.Call (Some lval, f, el, loc) ] }
          in
          (append_stmt_list lhs_sl [ stmt ], Some lhs_expr)
      | _ ->
          let instr = Cil.Set (lval, rhs_expr, loc) in
          (append_instr (rhs_sl @ lhs_sl) instr, Some lhs_expr))
  | C.MulAssign | C.DivAssign | C.RemAssign | C.AddAssign | C.SubAssign
  | C.ShlAssign | C.ShrAssign | C.AndAssign | C.XorAssign | C.OrAssign ->
      let drop_assign = function
        | C.MulAssign -> C.Mul
        | C.DivAssign -> C.Div
        | C.RemAssign -> C.Rem
        | C.AddAssign -> C.Add
        | C.SubAssign -> C.Sub
        | C.ShlAssign -> C.Shl
        | C.ShrAssign -> C.Shr
        | C.AndAssign -> C.And
        | C.XorAssign -> C.Xor
        | C.OrAssign -> C.Or
        | _ -> failwith "Invalid syntaxk"
      in
      let lval =
        match lhs_expr with Cil.Lval l -> l | _ -> failwith "invalid lhs"
      in
      let bop = drop_assign kind in
      let typ = Cil.typeOfLval lval in
      let rhs =
        Cil.BinOp (trans_binop lhs_expr rhs_expr bop, lhs_expr, rhs_expr, typ)
      in
      let stmt = Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rhs, loc) ]) in
      (rhs_sl @ lhs_sl @ [ stmt ], Some lhs_expr)
  | C.Comma -> (rhs_sl @ lhs_sl, Some rhs_expr)
  | C.Cmp | C.PtrMemD | C.PtrMemI | C.InvalidBinaryOperator ->
      failwith "unsupported expr"

and trans_call scope skip_lhs fundec_opt loc callee args =
  let fundec = Option.get fundec_opt in
  let callee_insts, callee_opt =
    trans_expr ~allow_undef:true scope fundec_opt loc AExp callee
  in
  let callee = match callee_opt with Some x -> x | None -> failwith "call" in
  let args_insts, args_exprs =
    List.fold_left
      (fun (args_insts, args_exprs) arg ->
        let insts, expr_opt = trans_expr scope fundec_opt loc AExp arg in
        let expr = match expr_opt with Some x -> x | None -> failwith "arg" in
        (args_insts @ insts, expr :: args_exprs))
      ([], []) args
  in
  let rec make_retvar t =
    match Cil.unrollType t with
    | (Cil.TFun (rt, _, _, _) | TPtr (TFun (rt, _, _, _), _))
      when (not (Cil.isVoidType rt)) && not skip_lhs ->
        let temp = (Cil.Var (Cil.makeTempVar fundec rt), Cil.NoOffset) in
        Some temp
    | Cil.TPtr ((TNamed (_, _) as t), a) ->
        make_retvar (Cil.TPtr (Cil.unrollType t, a))
    | _ -> None
  in
  let retvar = Cil.typeOf callee |> make_retvar in
  let retvar_exp =
    match retvar with Some x -> Some (Cil.Lval x) | _ -> None
  in
  let instr = Cil.Call (retvar, callee, List.rev args_exprs, loc) in
  (append_instr (callee_insts @ args_insts) instr, retvar_exp)

and trans_member scope fundec_opt loc base arrow field =
  match base with
  | Some b -> (
      let _, bexp = trans_expr scope fundec_opt loc ADrop b in
      match bexp with
      | Some e when arrow ->
          let typ = Cil.typeOf e in
          let fieldinfo =
            match Cil.unrollTypeDeep typ with
            | Cil.TPtr (TComp (comp, _), _) ->
                let name =
                  match field with
                  | C.Ast.FieldName f -> name_of_ident_ref f.desc
                  | _ -> "unknown"
                in
                List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
            | _ -> failwith "fail"
          in
          Cil.Lval
            (Cil.mkMem ~addr:e ~off:(Cil.Field (fieldinfo, Cil.NoOffset)))
      | Some (Cil.Lval lv) when not arrow -> (
          let typ = Cil.typeOfLval lv in
          match Cil.unrollTypeDeep typ with
          | Cil.TComp (comp, _) ->
              let name =
                match field with
                | C.Ast.FieldName f -> name_of_ident_ref f.desc
                | _ -> "unknown"
              in
              let fieldinfo =
                List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
              in
              Cil.Lval
                (Cil.addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv)
          | Cil.TPtr (TComp (comp, _), _) ->
              (* this case is counterintuitive but it's required to parse
                 the code referencing the anonymous struct inside struct *)
              let name =
                match field with
                | C.Ast.FieldName f -> name_of_ident_ref f.desc
                | _ -> "unknown"
              in
              let fieldinfo =
                List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
              in
              Cil.Lval
                (Cil.mkMem ~addr:(Option.get bexp)
                   ~off:(Cil.Field (fieldinfo, Cil.NoOffset)))
          | _ -> failwith "fail")
      | Some e ->
          CilHelper.s_location loc |> prerr_endline;
          CilHelper.s_exp e |> prerr_endline;
          failwith "error bexp = some e"
      | None ->
          CilHelper.s_location loc |> prerr_endline;
          failwith "error bexp = none")
  | None ->
      CilHelper.s_location loc |> prerr_endline;
      failwith "error base = none"

and trans_cond_op scope fundec_opt loc cond then_branch else_branch =
  let scope = Scope.enter_block scope in
  let cond_sl, cond_expr = trans_expr scope fundec_opt loc AExp cond in
  let then_sl, then_expr =
    match then_branch with
    | Some tb -> trans_expr scope fundec_opt loc ADrop tb
    | None -> ([], None)
  in
  let else_sl, else_expr = trans_expr scope fundec_opt loc ADrop else_branch in
  let cond_expr = Option.get cond_expr in
  match fundec_opt with
  | None ->
      if Cil.constFold false cond_expr |> Cil.isZero then
        match else_expr with
        | Some else_expr -> ([], Some (Cil.constFold false else_expr))
        | None -> ([], None)
      else if then_expr = None then ([], None)
      else ([], Some (Option.get then_expr |> Cil.constFold false))
  | Some fundec ->
      let typ =
        match (then_expr, else_expr) with
        | Some e, _ -> Cil.typeOf e
        | None, Some else_expr -> Cil.typeOf else_expr
        | _, _ -> Cil.intType
      in
      let vi, _ = create_local_variable scope fundec "tmp" typ in
      let var = (Cil.Var vi, Cil.NoOffset) in
      let bstmts =
        match then_expr with
        | Some e when CilHelper.eq_typ (Cil.typeOf e) typ ->
            append_instr then_sl (Cil.Set (var, e, loc))
        | Some e ->
            append_instr then_sl (Cil.Set (var, Cil.CastE (typ, e), loc))
        | None -> []
      in
      let tb = { Cil.battrs = []; bstmts } in
      let bstmts =
        match else_expr with
        | Some else_expr ->
            if CilHelper.eq_typ (Cil.typeOf else_expr) typ then
              append_instr else_sl (Cil.Set (var, else_expr, loc))
            else
              append_instr else_sl
                (Cil.Set (var, Cil.CastE (typ, else_expr), loc))
        | None -> else_sl
      in
      let fb = { Cil.battrs = []; bstmts } in
      let return_exp =
        match else_expr with
        | Some else_expr when CilHelper.eq_typ (Cil.typeOf else_expr) typ ->
            Some (Cil.Lval var)
        | _ -> Some (Cil.CastE (Cil.intType, Cil.Lval var))
      in
      if Cil.constFold false cond_expr |> Cil.isZero then
        (cond_sl @ fb.bstmts, return_exp)
      else if Cil.constFold false cond_expr |> CilHelper.is_constant_n 1 then
        (cond_sl @ tb.bstmts, return_exp)
      else
        (cond_sl @ [ Cil.mkStmt (Cil.If (cond_expr, tb, fb, loc)) ], return_exp)

and trans_unary_expr scope fundec_opt loc kind argument =
  match (kind, argument) with
  | C.SizeOf, C.Ast.ArgumentExpr e -> (
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.SizeOfE e)) | None -> ([], None))
  | C.SizeOf, C.Ast.ArgumentType t ->
      let typ = trans_type scope t in
      ([], Some (Cil.SizeOf typ))
  | C.AlignOf, C.Ast.ArgumentExpr e
  | C.VecStep, C.Ast.ArgumentExpr e
  | C.OpenMPRequiredSimdAlign, C.Ast.ArgumentExpr e
  | C.PreferredAlignOf, C.Ast.ArgumentExpr e -> (
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.AlignOfE e)) | None -> ([], None))
  | C.AlignOf, C.Ast.ArgumentType t
  | C.VecStep, C.Ast.ArgumentType t
  | C.OpenMPRequiredSimdAlign, C.Ast.ArgumentType t
  | C.PreferredAlignOf, C.Ast.ArgumentType t ->
      let typ = trans_type scope t in
      ([], Some (Cil.AlignOf typ))

let get_opt msg = function Some x -> x | None -> failwith msg

let goto_count = ref 0

module Chunk = struct
  module LabelMap = struct
    include Map.Make (String)

    let append xm ym = union (fun _ _ _ -> failwith "duplicated labels") xm ym
  end

  module GotoMap = struct
    include Map.Make (struct
      type t = Cil.stmt ref

      let compare = compare
    end)

    let append xm ym =
      union (fun _ _ _ -> failwith "duplicated goto targets") xm ym
  end

  type t = {
    stmts : Cil.stmt list;
    cases : Cil.stmt list;
    labels : Cil.stmt ref LabelMap.t;
    gotos : string GotoMap.t;
    user_typs : Cil.global list;
  }

  let empty =
    {
      stmts = [];
      cases = [];
      labels = LabelMap.empty;
      gotos = GotoMap.empty;
      user_typs = [];
    }

  let append x y =
    {
      stmts = append_stmt_list x.stmts y.stmts;
      cases = x.cases @ y.cases;
      labels = LabelMap.append x.labels y.labels;
      gotos = GotoMap.append x.gotos y.gotos;
      user_typs = x.user_typs @ y.user_typs;
    }
end

class replaceGotoVisitor gotos labels =
  object
    inherit Cil.nopCilVisitor

    method! vstmt stmt =
      match stmt.Cil.skind with
      | Cil.Goto (placeholder, loc) -> (
          match Chunk.GotoMap.find placeholder gotos with
          | label ->
              let target =
                try Chunk.LabelMap.find label labels
                with Not_found ->
                  failwith
                    (CilHelper.s_location loc ^ ": label " ^ label
                   ^ " not found")
              in
              stmt.Cil.skind <- Cil.Goto (target, loc);
              Cil.DoChildren
          | exception Not_found -> Cil.DoChildren)
      | _ -> Cil.DoChildren
  end

let append_label chunk label loc in_origin =
  let l = Cil.Label (label, loc, in_origin) in
  match chunk.Chunk.stmts with
  | h :: _ ->
      h.labels <- h.labels @ [ l ];
      { chunk with labels = Chunk.LabelMap.add label (ref h) chunk.labels }
  (*       chunk.labels <- Chunk.LabelMap.add label (ref h) chunk.labels; *)
  (*       chunk *)
  | [] ->
      let h = Cil.mkStmt (Cil.Instr []) in
      h.labels <- [ l ];
      {
        chunk with
        stmts = [ h ];
        labels = Chunk.LabelMap.add label (ref h) chunk.labels;
      }
(*chunk.stmts <- [ h ];
  chunk.labels <- Chunk.LabelMap.add label (ref h) chunk.labels;
  chunk*)

let trans_storage decl =
  match C.Ast.cursor_of_node decl |> C.cursor_get_storage_class with
  | C.Extern -> Cil.Extern
  | C.Register -> Cil.Register
  | C.Static -> Cil.Static
  | _ -> Cil.NoStorage

let trans_goto loc label =
  let dummy_instr =
    Cil.Asm
      ( [],
        [ "dummy goto target " ^ string_of_int !goto_count ],
        [],
        [],
        [],
        Cil.locUnknown )
  in
  goto_count := !goto_count + 1;
  let placeholder = Cil.mkStmt (Cil.Instr [ dummy_instr ]) in
  let reference = ref placeholder in
  {
    Chunk.empty with
    stmts = [ Cil.mkStmt (Cil.Goto (reference, loc)) ];
    gotos = Chunk.GotoMap.add reference label Chunk.GotoMap.empty;
  }

let att_nothrow = Cil.Attr ("nothrow", [])

let att_gnu_inline = Cil.Attr ("gnu_inline", [])

let trans_decl_attribute attrs =
  List.fold_left
    (fun attrs (attr : C.Ast.attribute_desc C.Ast.node) ->
      match attr.C.Ast.desc with
      | GNUInline _ -> att_gnu_inline :: attrs
      | NoThrow _ -> att_nothrow :: attrs
      | _ -> attrs)
    [] attrs

let rec trans_stmt scope fundec (stmt : C.Ast.stmt) : Chunk.t * Scope.t =
  let loc = trans_location stmt in
  match stmt.C.Ast.desc with
  | Null | AttributedStmt _ ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr []) ] }, scope)
  | Compound sl ->
      (* CIL does not need to have local blocks because all variables have unique names *)
      trans_compound scope fundec sl
  | For fdesc ->
      trans_for scope fundec loc fdesc.init fdesc.condition_variable fdesc.cond
        fdesc.inc fdesc.body
  | ForRange _ -> failwith ("Unsupported syntax : " ^ CilHelper.s_location loc)
  | If desc ->
      trans_if scope fundec loc desc.init desc.condition_variable desc.cond
        desc.then_branch desc.else_branch
  | Switch desc ->
      trans_switch scope fundec loc desc.init desc.condition_variable desc.cond
        desc.body
  | Case desc -> trans_case scope fundec loc desc.lhs desc.body
  | Default stmt -> trans_default scope fundec loc stmt
  | While desc ->
      trans_while scope fundec loc desc.condition_variable desc.cond desc.body
  | Do desc -> trans_do scope fundec loc desc.body desc.cond
  | Label desc -> trans_label scope fundec loc desc.label desc.body
  | Goto label -> (trans_goto loc label, scope)
  | IndirectGoto _ ->
      failwith ("Unsupported syntax (IndirectGoto): " ^ CilHelper.s_location loc)
  | Continue ->
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Continue loc) ] },
        scope )
  | Break ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Break loc) ] }, scope)
  | Asm desc ->
      let instr =
        Cil.Asm ([], [ desc.asm_string ], [], [], [], Cil.locUnknown)
      in
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr [ instr ]) ] },
        scope )
  | Return None ->
      let stmts = [ Cil.mkStmt (Cil.Return (None, loc)) ] in
      ({ Chunk.empty with stmts }, scope)
  | Return (Some e) -> (
      let sl, expr_opt = trans_expr scope (Some fundec) loc AExp e in
      match expr_opt with
      | None ->
          ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr []) ] },
            scope )
      | Some expr ->
          let stmts =
            if sl = [] then [ Cil.mkStmt (Cil.Return (Some expr, loc)) ]
            else sl @ [ Cil.mkStmt (Cil.Return (Some expr, loc)) ]
          in
          ({ Chunk.empty with stmts }, scope))
  | Decl dl ->
      let stmts, user_typs, scope =
        trans_var_decl_list scope fundec loc AExp dl
      in
      ({ Chunk.empty with stmts; user_typs }, scope)
  | Expr e ->
      (* skip_lhs is true here: a function is called at the top-most level
       * without a return variable *)
      let stmts, _ =
        trans_expr ~skip_lhs:true scope (Some fundec) loc ADrop e
      in
      ({ Chunk.empty with stmts }, scope)
  | Try _ -> failwith ("Unsupported syntax (Try): " ^ CilHelper.s_location loc)
  | UnknownStmt (_, _) ->
      (*       C.Ast.pp_stmt F.err_formatter stmt ; *)
      let stmts = [ Cil.dummyStmt ] in
      ({ Chunk.empty with stmts }, scope)

and trans_compound scope fundec sl =
  let scope = Scope.enter_block scope in
  ( List.fold_left
      (fun (l, scope) s ->
        let chunk, scope = trans_stmt scope fundec s in
        (Chunk.append l chunk, scope))
      (Chunk.empty, scope) sl
    |> fst,
    scope )

and trans_var_decl_list scope fundec loc action (dl : C.Ast.decl list) =
  List.fold_left
    (fun (sl, user_typs, scope) (d : C.Ast.decl) ->
      match d.C.Ast.desc with
      | C.Ast.Var desc ->
          let storage = trans_storage d in
          let decl_stmts, scope =
            trans_var_decl ~storage scope fundec loc action desc
          in
          (sl @ decl_stmts, user_typs, scope)
      | C.Ast.RecordDecl rdecl when rdecl.C.Ast.complete_definition ->
          let is_struct = rdecl.keyword = C.Struct in
          let cursor = C.Ast.cursor_of_decoration d.decoration in
          let new_name, is_new_anon = new_record_id is_struct rdecl cursor in
          let callback compinfo =
            List.fold_left
              (fun fl (decl : C.Ast.decl) ->
                match decl.C.Ast.desc with
                | C.Ast.Field _ -> fl @ [ trans_field_decl scope compinfo decl ]
                | C.Ast.IndirectField _ ->
                    fl @ trans_indirect_field_decl scope compinfo decl
                | _ -> fl)
              [] rdecl.fields
          in
          let scope =
            if is_new_anon then
              let compinfo = Cil.mkCompInfo is_struct new_name callback [] in
              let tcomp = Cil.TComp (compinfo, []) in
              Scope.add_comp new_name tcomp scope
            else scope
          in
          let globals, scope = trans_global_decl ~new_name scope d in
          (sl, user_typs @ globals, scope)
      | C.Ast.RecordDecl rdecl ->
          let is_struct = rdecl.keyword = C.Struct in
          let cursor = C.Ast.cursor_of_decoration d.decoration in
          let name, is_new_anon = new_record_id is_struct rdecl cursor in
          let callback compinfo =
            List.fold_left
              (fun fl (decl : C.Ast.decl) ->
                match decl.C.Ast.desc with
                | C.Ast.Field _ -> fl @ [ trans_field_decl scope compinfo decl ]
                | C.Ast.IndirectField _ ->
                    fl @ trans_indirect_field_decl scope compinfo decl
                | _ -> fl)
              [] rdecl.fields
          in
          let scope =
            if is_new_anon then
              let compinfo = Cil.mkCompInfo is_struct name callback [] in
              let tcomp = Cil.TComp (compinfo, []) in
              Scope.add_comp name tcomp scope
            else scope
          in
          if Scope.mem_typ name scope then (sl, user_typs, scope)
          else
            let globals, scope = trans_global_decl ~new_name:name scope d in
            (sl, user_typs @ globals, scope)
      | TypedefDecl tdecl ->
          let ttype = trans_type scope tdecl.underlying_type in
          let tinfo = { Cil.tname = tdecl.name; ttype; treferenced = false } in
          let scope =
            Scope.add_type tdecl.name (Cil.TNamed (tinfo, [])) scope
          in
          (sl, user_typs @ [ Cil.GType (tinfo, loc) ], scope)
      | EnumDecl edecl ->
          let globals, scope =
            trans_global_decl ~new_name:(new_enum_id edecl.name) scope d
          in
          (sl, user_typs @ globals, scope)
      | Function _ ->
          (* if the program is valid, there must be the corresponding def somewhere *)
          (sl, user_typs, scope)
      | Field _ | IndirectField _ | EmptyDecl | AccessSpecifier _ | Namespace _
      | UsingDirective _ | UsingDeclaration _ | Constructor _ | Destructor _
      | LinkageSpec _ | TemplateTemplateParameter _ | Friend _
      | NamespaceAlias _ | Directive _ | StaticAssert _ | TypeAlias _
      | Decomposition _
      | UnknownDecl (_, _) ->
          L.warn ~to_consol:false "Unknown var decl %s\n"
            (CilHelper.s_location loc);
          (sl, [], scope)
      | TemplateDecl _ | TemplatePartialSpecialization _ | CXXMethod _ ->
          failwith "Unsupported C++ features"
      | Concept _ | Export _ -> failwith "new cases: Concept | Export")
    ([], [], scope) dl

and trans_var_decl ?(storage = Cil.NoStorage) (scope : Scope.t) fundec loc
    action (desc : C.Ast.var_decl_desc) =
  let typ = trans_type scope desc.C.Ast.var_type in
  let varinfo, scope = create_local_variable scope fundec desc.var_name typ in
  varinfo.vstorage <- storage;
  match desc.var_init with
  | Some e ->
      let lv = (Cil.Var varinfo, Cil.NoOffset) in
      handle_stmt_init scope typ fundec loc action lv e
  | _ -> ([], scope)

and handle_stmt_init scope typ fundec loc action lv (e : C.Ast.expr) =
  let is_primitive_typ typ =
    match Cil.unrollType typ with Cil.TComp (_, _) -> false | _ -> true
  in
  let is_struct_typ typ = not (is_primitive_typ typ) in
  match (e.C.Ast.desc, Cil.unrollType typ) with
  | C.Ast.InitList _, Cil.TArray (_, None, _) | C.Ast.InitList _, Cil.TPtr _ ->
      ([], scope)
  (* primitive array *)
  | C.Ast.InitList el, Cil.TArray (arr_typ, Some arr_exp, _)
    when is_primitive_typ arr_typ ->
      mk_arr_stmt scope fundec loc action lv arr_exp el
  (* struct array *)
  | C.Ast.InitList el, Cil.TArray (arr_typ, Some arr_exp, _)
    when is_struct_typ arr_typ ->
      let ci =
        match Cil.unrollType arr_typ with
        | Cil.TComp (ci, _) -> ci
        | _ -> failwith "expected only struct type"
      in
      let unroll_nested_init scope idx e =
        if is_init_list e then
          let lv =
            Cil.addOffsetLval (Cil.Index (Cil.integer idx, Cil.NoOffset)) lv
          in
          handle_stmt_init scope arr_typ fundec loc action lv e
        else
          let stmts, _, scope =
            mk_array_stmt el (List.hd ci.cfields) loc fundec action lv scope
              arr_typ (Some arr_exp) false
          in
          (stmts, scope)
      in
      let stmts, scope, _ =
        List.fold_left
          (fun (stmts, scope, idx) e ->
            let stmts', scope' = unroll_nested_init scope idx e in
            (stmts @ stmts', scope', idx + 1))
          ([], scope, 0) el
      in
      (stmts, scope)
  (* struct *)
  | C.Ast.InitList el, Cil.TComp (ci, _) ->
      let stmts, _, scope =
        mk_local_struct_init scope ci.cfields fundec action loc lv el
      in
      (stmts, scope)
  (* primitive init list (contains only one element) *)
  | C.Ast.InitList el, _ ->
      let e =
        if List.length el <> 1 then
          failwith "primitive literal init list should be only one element"
        else List.hd el
      in
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let instr = Cil.Set (lv, expr, loc) in
      (append_instr sl_expr instr, scope)
  (* primitive *)
  | _ ->
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let instr = Cil.Set (lv, expr, loc) in
      (append_instr sl_expr instr, scope)

and mk_while_stmt arr_len loc tmp_var_expr tmp_var_lval unary_plus_expr
    var_stmts =
  let cond_expr =
    Cil.BinOp (Cil.Ge, tmp_var_expr, Cil.integer arr_len, Cil.intType)
  in
  let unary_plus_instr =
    Cil.Instr [ Cil.Set (tmp_var_lval, unary_plus_expr, loc) ]
  in
  let unary_plus_stmt = Cil.mkStmt unary_plus_instr in
  [
    Cil.mkStmt
      (Cil.Loop
         ( Cil.mkBlock
             (Cil.mkStmt
                (Cil.If
                   ( cond_expr,
                     Cil.mkBlock [ Cil.mkStmt (Break loc) ],
                     Cil.mkBlock [],
                     loc ))
              :: var_stmts
             @ [ unary_plus_stmt ]),
           loc,
           None,
           None ));
  ]

and mk_tmp_var fundec loc expr_list_len scope =
  let vi, scope = create_local_variable scope fundec "tmp" Cil.uintType in
  let tmp_var_lval = (Cil.Var vi, Cil.NoOffset) in
  let tmp_var_instr =
    Cil.Set
      (tmp_var_lval, Cil.CastE (Cil.uintType, Cil.integer expr_list_len), loc)
  in
  let tmp_var_stmt = Cil.mkStmt (Cil.Instr [ tmp_var_instr ]) in
  let tmp_var_expr = Cil.Lval tmp_var_lval in

  (* tmp++ *)
  let one = Cil.BinOp (Cil.PlusA, tmp_var_expr, Cil.one, Cil.intType) in
  (tmp_var_lval, tmp_var_expr, tmp_var_stmt, one, scope)

(* int arr[5] = {1}
 * ==>
 * int arr[5];
 * arr[0] = 1;
 * tmp = 1;
 * while (tmp < 5)
 *   arr[tmp] = 0;    // for all unspecified element, assign 0
 *)
and mk_arr_stmt scope fundec loc action lv len_exp el =
  let arr_len =
    match len_exp with
    | Cil.Const (CInt64 (v, _, _)) -> Int64.to_int v
    | _ -> failwith "not expected"
  in
  let arr_init idx_list =
    let instr_list =
      List.fold_left
        (fun (instr_list, expr_remainders) idx ->
          let e = List.hd expr_remainders in
          let _, expr_opt = trans_expr scope (Some fundec) loc action e in
          let expr = get_opt "var_decl" expr_opt in
          let lv =
            Cil.addOffsetLval (Cil.Index (Cil.integer idx, Cil.NoOffset)) lv
          in
          let instr = Cil.Set (lv, expr, loc) in
          (instr :: instr_list, List.tl expr_remainders))
        ([], el) idx_list
      |> fst
    in
    [ Cil.mkStmt (Cil.Instr (List.rev instr_list)) ]
  in
  let idx_list =
    if List.length el >= arr_len then List.init arr_len Fun.id
    else List.init (List.length el) Fun.id
  in
  if List.length el < arr_len then
    let sl = arr_init idx_list in
    (* tmp var *)
    let vi, scope = create_local_variable scope fundec "tmp" Cil.uintType in
    let tmp_var_lval = (Cil.Var vi, Cil.NoOffset) in
    let tmp_var_instr =
      Cil.Set
        ( tmp_var_lval,
          Cil.CastE (Cil.uintType, Cil.integer (List.length el)),
          loc )
    in
    let tmp_var_stmt = Cil.mkStmt (Cil.Instr [ tmp_var_instr ]) in
    let tmp_var_expr = Cil.Lval tmp_var_lval in

    (* tmp++ *)
    let one = Cil.BinOp (Cil.PlusA, tmp_var_expr, Cil.one, Cil.intType) in

    (* arr[tmp] = 0 *)
    let lv = Cil.addOffsetLval (Cil.Index (tmp_var_expr, Cil.NoOffset)) lv in
    let var_instr = Cil.Instr [ Cil.Set (lv, Cil.integer 0, loc) ] in
    let var_stmt = Cil.mkStmt var_instr in

    (* while *)
    let cond_expr =
      Cil.BinOp (Cil.Ge, tmp_var_expr, Cil.integer arr_len, Cil.intType)
    in
    let unary_plus_instr = Cil.Instr [ Cil.Set (tmp_var_lval, one, loc) ] in
    let unary_plus_stmt = Cil.mkStmt unary_plus_instr in
    let while_stmt =
      [
        Cil.mkStmt
          (Cil.Loop
             ( Cil.mkBlock
                 [
                   Cil.mkStmt
                     (Cil.If
                        ( cond_expr,
                          Cil.mkBlock [ Cil.mkStmt (Break loc) ],
                          Cil.mkBlock [],
                          loc ));
                   var_stmt;
                   unary_plus_stmt;
                 ],
               loc,
               None,
               None ));
      ]
    in
    (sl @ [ tmp_var_stmt ] @ while_stmt, scope)
  else (arr_init idx_list, scope)

and mk_local_struct_init scope cfields fundec action loc lv expr_list =
  let origin_cfields = cfields in
  let rec loop scope union_flag cfields expr_list fis stmts idx_list idx =
    match (cfields, expr_list) with
    | f :: fl, e :: el ->
        if union_flag then
          loop scope union_flag fl expr_list fis stmts ((idx + 1) :: idx_list)
            (idx + 1)
        else if f.Cil.fcomp.cstruct then
          if is_init_list e then
            let lv = Cil.addOffsetLval (Cil.Field (f, Cil.NoOffset)) lv in
            let stmts', scope =
              handle_stmt_init scope f.ftype fundec loc action lv e
            in
            loop scope union_flag fl el (f :: fis) (stmts @ stmts')
              ((idx + 1) :: idx_list) (idx + 1)
          else
            let field, i, is_find = grab_matching_field origin_cfields f e in
            let f = List.hd field in
            let i = if is_find >= 0 then i else idx + 1 in
            let stmts', expr_remainders, scope =
              mk_init_stmt scope loc fundec action f lv expr_list
            in
            loop scope union_flag fl expr_remainders (f :: fis) (stmts @ stmts')
              (i :: idx_list) (idx + 1)
        else if is_init_list e then
          let lv = Cil.addOffsetLval (Cil.Field (f, Cil.NoOffset)) lv in
          let stmts', scope =
            handle_stmt_init scope f.ftype fundec loc action lv e
          in
          loop scope true fl el (f :: fis) (stmts @ stmts')
            ((idx + 1) :: idx_list) (idx + 1)
        else
          (* union *)
          let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
          let expr = get_opt "var_decl" expr_opt in
          let lv = Cil.addOffsetLval (Cil.Field (f, Cil.NoOffset)) lv in
          let instr = Cil.Set (lv, expr, loc) in
          loop scope true fl el (f :: fis)
            (append_instr sl_expr instr)
            ((idx + 1) :: idx_list) (idx + 1)
    | f :: fl, [] ->
        if union_flag then
          loop scope union_flag fl [] fis stmts ((idx + 1) :: idx_list) (idx + 1)
        else if f.fcomp.cstruct then
          let stmts', expr_remainders, scope =
            mk_init_stmt scope loc fundec action f lv expr_list
          in
          loop scope union_flag fl expr_remainders (f :: fis) (stmts @ stmts')
            ((idx + 1) :: idx_list) (idx + 1)
        else
          let expr = Cil.integer 0 in
          let lv = Cil.addOffsetLval (Cil.Field (f, Cil.NoOffset)) lv in
          let instr = Cil.Set (lv, expr, loc) in
          let stmt = Cil.mkStmt (Cil.Instr [ instr ]) in
          loop scope true fl [] (f :: fis)
            (stmts @ [ stmt ])
            ((idx + 1) :: idx_list) (idx + 1)
    | [], _ -> (stmts, expr_list, scope, idx_list, idx)
  in
  let stmts, expr_list, scope, idx_list, _ =
    loop scope false cfields expr_list [] [] [] 0
  in
  if List.length stmts = List.length idx_list then
    let stmts = sort_list_with_index (List.rev stmts) idx_list |> List.rev in
    (stmts, expr_list, scope)
  else (stmts, expr_list, scope)

and mk_init_stmt scope loc fundec action fi lv expr_list =
  (* for uninitaiized *)
  match (Cil.unrollType fi.Cil.ftype, expr_list) with
  | Cil.TInt (ikind, _), [] ->
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, Cil.kinteger ikind 0, loc) in
      (append_instr [] instr, [], scope)
  | Cil.TFloat (fkind, _), [] ->
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, Cil.Const (Cil.CReal (0., fkind, None)), loc) in
      (append_instr [] instr, [], scope)
  | Cil.TPtr (typ, _), [] ->
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr =
        Cil.Set (lv, Cil.CastE (TPtr (typ, []), Cil.integer 0), loc)
      in
      (append_instr [] instr, [], scope)
  | Cil.TEnum (_, _), [] ->
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, Cil.integer 0, loc) in
      (append_instr [] instr, [], scope)
  (* for initaiized *)
  | Cil.TInt (_, _), e :: el ->
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, expr, loc) in
      (append_instr sl_expr instr, el, scope)
  | Cil.TFloat (_, _), e :: el ->
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, expr, loc) in
      (append_instr sl_expr instr, el, scope)
  | Cil.TPtr (typ, attr), e :: el -> (
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let actual_typ = Cil.unrollTypeDeep typ in
      match actual_typ with
      | Cil.TFun (_, _, _, _) ->
          (* function pointer *)
          let instr =
            Cil.Set (lv, Cil.CastE (Cil.TPtr (actual_typ, attr), expr), loc)
          in
          (append_instr sl_expr instr, el, scope)
      | _ ->
          let instr = Cil.Set (lv, expr, loc) in
          (append_instr sl_expr instr, el, scope))
  (* common *)
  | Cil.TComp (ci, _), _ ->
      (* struct in struct *)
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      mk_local_struct_init scope ci.cfields fundec action loc lv expr_list
  | Cil.TArray (arr_type, arr_exp, _), _ ->
      mk_array_stmt expr_list fi loc fundec action lv scope arr_type arr_exp
        true
  | Cil.TEnum (_, _), e :: el ->
      let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let lv = Cil.addOffsetLval (Cil.Field (fi, Cil.NoOffset)) lv in
      let instr = Cil.Set (lv, expr, loc) in
      (append_instr sl_expr instr, el, scope)
  | _ -> failwith "not expected"

and mk_tcomp_array_stmt stmts expr_list expr_remainders o ci fi fundec action
    loc tmp_var lv flags primitive_arr_remainders scope attach_flag =
  let stmts', expr_remainders', tmp_var, flags, scope =
    if (expr_list <> [] && expr_remainders <> []) || flags.skip_while then
      let lv =
        if attach_flag then
          Cil.addOffsetLval
            (Cil.Field (fi, Cil.Index (Cil.integer o, Cil.NoOffset)))
            lv
        else Cil.addOffsetLval (Cil.Index (Cil.integer o, Cil.NoOffset)) lv
      in
      let stmts', expr_remainders', scope =
        mk_local_struct_init scope ci.Cil.cfields fundec action loc lv
          expr_remainders
      in
      let flags =
        if expr_list <> [] && expr_remainders <> [] then
          let _ =
            flags.total_initialized_items_len <-
              max flags.total_initialized_items_len (List.length stmts')
          in
          flags
        else flags
      in
      (stmts', expr_remainders', tmp_var, flags, scope)
    else
      let _ =
        if o = 0 then flags.skip_while <- true else flags.while_flag <- true
      in
      if not flags.skip_while then (
        let tmp_var_lval, tmp_var_expr, tmp_var_stmt, unary_plus_expr, scope =
          mk_tmp_var fundec loc (List.length expr_list) scope
        in
        let tmp_var =
          Some { tmp_var_lval; tmp_var_expr; tmp_var_stmt; unary_plus_expr }
        in
        let lv =
          if attach_flag then
            Cil.addOffsetLval
              (Cil.Field (fi, Cil.Index (tmp_var_expr, Cil.NoOffset)))
              lv
          else Cil.addOffsetLval (Cil.Index (tmp_var_expr, Cil.NoOffset)) lv
        in
        flags.tmp_var_cond_update <- flags.tmp_var_cond_update + 1;
        let stmts', expr_remainders', scope =
          mk_local_struct_init scope ci.cfields fundec action loc lv
            expr_remainders
        in
        flags.total_initialized_items_len <-
          max flags.total_initialized_items_len (List.length stmts');
        (stmts', expr_remainders', tmp_var, flags, scope))
      else
        let lv =
          if attach_flag then
            Cil.addOffsetLval
              (Cil.Field (fi, Cil.Index (Cil.integer o, Cil.NoOffset)))
              lv
          else Cil.addOffsetLval (Cil.Index (Cil.integer o, Cil.NoOffset)) lv
        in
        let stmts', expr_remainders', scope =
          mk_local_struct_init scope ci.cfields fundec action loc lv
            expr_remainders
        in
        (stmts', expr_remainders', tmp_var, flags, scope)
  in
  flags.terminate_flag <- expr_remainders' = [];
  ( stmts @ stmts',
    primitive_arr_remainders,
    expr_remainders',
    scope,
    tmp_var,
    flags,
    o + 1 )

and mk_primitive_array_stmt stmts expr_list expr_remainders o arr_type arr_len
    lv fi fundec action loc tmp_var flags primitive_arr_remainders scope =
  match expr_remainders with
  | e :: remainders when expr_list <> [] ->
      let _, expr_opt = trans_expr scope (Some fundec) loc action e in
      let expr = get_opt "var_decl" expr_opt in
      let lv1 =
        Cil.addOffsetLval
          (Cil.Field (fi, Cil.Index (Cil.integer o, Cil.NoOffset)))
          lv
      in
      let instr = Cil.Set (lv1, Cil.CastE (arr_type, expr), loc) in
      flags.total_initialized_items_len <-
        max flags.total_initialized_items_len 1;
      if arr_len > o + 1 && remainders = [] then (
        let tmp_var_lval, tmp_var_expr, tmp_var_stmt, unary_plus_expr, scope =
          mk_tmp_var fundec loc (o + 1) scope
        in
        let lv2 =
          Cil.addOffsetLval
            (Cil.Field (fi, Cil.Index (tmp_var_expr, Cil.NoOffset)))
            lv
        in
        let instr_remainder = Cil.Set (lv2, Cil.integer 0, loc) in
        let stmt_remainder = append_instr [] instr_remainder in
        let while_stmt =
          mk_while_stmt arr_len loc tmp_var_expr tmp_var_lval unary_plus_expr
            stmt_remainder
        in
        flags.terminate_flag <- true;
        ( stmts @ append_instr [] instr,
          tmp_var_stmt :: while_stmt,
          remainders,
          scope,
          tmp_var,
          flags,
          o + 1 ))
      else
        ( stmts @ append_instr [] instr,
          primitive_arr_remainders,
          remainders,
          scope,
          tmp_var,
          flags,
          o + 1 )
  | _ ->
      if flags.terminate_flag then
        ( stmts,
          primitive_arr_remainders,
          expr_remainders,
          scope,
          tmp_var,
          flags,
          o )
      else
        let lv3 =
          Cil.addOffsetLval
            (Cil.Field (fi, Cil.Index (Cil.integer o, Cil.NoOffset)))
            lv
        in
        let instr = Cil.Set (lv3, Cil.CastE (arr_type, Cil.integer 0), loc) in
        ( stmts @ append_instr [] instr,
          primitive_arr_remainders,
          expr_remainders,
          scope,
          tmp_var,
          flags,
          o + 1 )

and mk_array_stmt expr_list fi loc fundec action lv scope arr_type arr_exp
    attach_flag =
  let len_exp = Option.get arr_exp in
  let arr_len =
    match len_exp with
    | Cil.Const (Cil.CInt64 (v, _, _)) -> Int64.to_int v
    | _ -> failwith "not expected"
  in
  let flags =
    {
      tmp_var_cond_update = 0;
      skip_while = false;
      while_flag = false;
      total_initialized_items_len = 0;
      terminate_flag = false;
    }
  in
  let empty_list = List.init arr_len (fun idx -> idx) in
  let ( var_stmts,
        primitive_arr_remainders,
        expr_remainders,
        scope,
        tmp_var,
        flags,
        _ ) =
    List.fold_left
      (fun ( stmts,
             primitive_arr_remainders,
             expr_remainders,
             scope,
             tmp_var,
             flags,
             o ) _ ->
        match Cil.unrollType arr_type with
        | Cil.TComp (ci, _) ->
            mk_tcomp_array_stmt stmts expr_list expr_remainders o ci fi fundec
              action loc tmp_var lv flags primitive_arr_remainders scope
              attach_flag
        | _ ->
            mk_primitive_array_stmt stmts expr_list expr_remainders o arr_type
              arr_len lv fi fundec action loc tmp_var flags
              primitive_arr_remainders scope)
      ([], [], expr_list, scope, None, flags, 0)
      empty_list
  in
  if flags.while_flag then (
    let first_half_stmts =
      BatList.take flags.total_initialized_items_len var_stmts
    in
    let last_half_stmts =
      BatList.drop flags.total_initialized_items_len var_stmts
    in
    let tmp_var = Option.get tmp_var in
    let while_stmt =
      mk_while_stmt arr_len loc tmp_var.tmp_var_expr tmp_var.tmp_var_lval
        tmp_var.unary_plus_expr last_half_stmts
    in
    let tmp_var_cond_back_patch =
      Cil.Set
        ( tmp_var.tmp_var_lval,
          Cil.CastE (Cil.uintType, Cil.integer flags.tmp_var_cond_update),
          loc )
    in
    tmp_var.tmp_var_stmt.skind <- Cil.Instr [ tmp_var_cond_back_patch ];
    ( first_half_stmts @ [ tmp_var.tmp_var_stmt ] @ while_stmt,
      expr_remainders,
      scope ))
  else (var_stmts @ primitive_arr_remainders, expr_remainders, scope)

and trans_var_decl_opt scope fundec loc (vdecl : C.Ast.var_decl option) =
  match vdecl with
  | Some v -> trans_var_decl scope fundec loc AExp v.C.Ast.desc
  | None -> ([], scope)

and trans_for scope fundec loc init cond_var cond inc body =
  let scope = Scope.enter_block scope in
  let init_stmt, scope = trans_stmt_opt scope fundec init in
  let decl_stmt, scope = trans_var_decl_opt scope fundec loc cond_var in
  let cond_expr =
    match cond with
    | Some e ->
        trans_expr scope (Some fundec) loc AExp e |> snd |> get_opt "for_cond"
    | None -> Cil.one
  in
  let break_stmt = Cil.mkBlock [ Cil.mkStmt (Cil.Break loc) ] in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc))
    :: body_stmt.Chunk.stmts
  in
  let block = { Cil.battrs = []; bstmts } in
  let inc_stmt = trans_stmt_opt scope fundec inc |> fst in
  let stmts =
    decl_stmt @ init_stmt.Chunk.stmts
    @ [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ]
    @ inc_stmt.Chunk.stmts
  in
  let cases = init_stmt.cases @ body_stmt.cases @ inc_stmt.cases in
  ( {
      Chunk.stmts;
      cases;
      labels = body_stmt.labels;
      gotos = body_stmt.gotos;
      user_typs = body_stmt.user_typs;
    },
    scope )

and trans_while scope fundec loc condition_variable cond body =
  let decl_stmt, scope =
    trans_var_decl_opt scope fundec loc condition_variable
  in
  let cond_expr =
    trans_expr scope (Some fundec) loc AExp cond |> snd |> get_opt "while_cond"
  in
  let break_stmt = Cil.mkBlock [ Cil.mkStmt (Cil.Break loc) ] in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    match Cil.constFold false cond_expr |> Cil.isInteger with
    | Some i64 when Cil.i64_to_int i64 = 1 -> body_stmt.Chunk.stmts
    | _ ->
        Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc))
        :: body_stmt.Chunk.stmts
  in
  let block = { Cil.battrs = []; bstmts } in
  let stmts = decl_stmt @ [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ] in
  ( {
      Chunk.stmts;
      cases = body_stmt.cases;
      labels = body_stmt.labels;
      gotos = body_stmt.gotos;
      user_typs = body_stmt.user_typs;
    },
    scope )

and trans_do scope fundec loc body cond =
  let cond_expr =
    trans_expr scope (Some fundec) loc AExp cond |> snd |> get_opt "do_cond"
  in
  let break_stmt = Cil.mkStmt (Cil.Break loc) in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    match Cil.constFold false cond_expr |> Cil.isInteger with
    | Some i64 when Cil.i64_to_int i64 = 1 -> body_stmt.Chunk.stmts
    | Some i64 when Cil.i64_to_int i64 = 0 ->
        body_stmt.Chunk.stmts @ [ break_stmt ]
    | _ ->
        let break_stmt = Cil.mkBlock [ break_stmt ] in
        body_stmt.Chunk.stmts
        @ [ Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc)) ]
  in

  let block = { Cil.battrs = []; bstmts } in
  let stmts = [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ] in
  ( {
      Chunk.stmts;
      cases = body_stmt.cases;
      labels = body_stmt.labels;
      gotos = body_stmt.gotos;
      user_typs = body_stmt.user_typs;
    },
    scope )

and trans_if scope fundec loc init cond_var cond then_branch else_branch =
  let init_stmt = trans_stmt_opt scope fundec init |> fst in
  let decl_stmt, scope = trans_var_decl_opt scope fundec loc cond_var in
  let cond_sl, cond_expr = trans_expr scope (Some fundec) loc AExp cond in
  let then_stmt = trans_block scope fundec then_branch in
  let else_stmt =
    match else_branch with
    | Some s ->
        let ans = trans_block scope fundec s in
        ans
    | None -> Chunk.empty
  in
  let duplicate chunk =
    if
      chunk.Chunk.cases <> []
      || not (Chunk.LabelMap.is_empty chunk.Chunk.labels)
    then raise (Failure "cannot duplicate: has labels")
    else
      let count =
        List.fold_left
          (fun c stmt ->
            match stmt.Cil.skind with
            | Cil.If _ | Cil.Switch _ | Cil.Loop _ | Cil.Block _ ->
                raise (Failure "cannot duplicate: complex stmt")
            | Cil.Instr il -> c + List.length il
            | _ -> c)
          0 chunk.Chunk.stmts
      in
      if count > 5 then raise (Failure "cannot duplicate: too many instr")
      else { Chunk.empty with stmts = chunk.Chunk.stmts }
  in
  (* Reference: https://github.com/cil-project/cil/blob/936b04103eb573f320c6badf280e8bb17f6e7b26/src/frontc/cabs2cil.ml#L4837 *)
  let rec compile_cond scope ce st sf =
    match ce with
    | Cil.BinOp (Cil.LAnd, ce1, ce2, _) ->
        let scope, sf1, sf2 =
          try (scope, sf, duplicate sf)
          with Failure _ ->
            let lab, scope = create_label scope "_L" in
            (scope, trans_goto loc lab, append_label sf lab loc false)
        in
        let scope, st' = compile_cond scope ce2 st sf1 in
        compile_cond scope ce1 st' sf2
    | Cil.BinOp (Cil.LOr, ce1, ce2, _) ->
        let scope, st1, st2 =
          try (scope, st, duplicate st)
          with Failure _ ->
            let lab, scope = create_label scope "_L" in
            (scope, trans_goto loc lab, append_label st lab loc false)
        in
        let scope, sf' = compile_cond scope ce2 st1 sf in
        compile_cond scope ce1 st2 sf'
    | _ ->
        let then_block = { Cil.battrs = []; bstmts = st.stmts } in
        let else_block = { Cil.battrs = []; bstmts = sf.stmts } in
        ( scope,
          {
            Chunk.stmts =
              [ Cil.mkStmt (Cil.If (ce, then_block, else_block, loc)) ];
            labels = Chunk.LabelMap.append st.labels sf.labels;
            gotos = Chunk.GotoMap.append st.gotos sf.gotos;
            cases = [];
            user_typs = init_stmt.user_typs;
          } )
  in
  let if_chunk =
    match cond_expr with
    | Some cond_expr -> compile_cond scope cond_expr then_stmt else_stmt |> snd
    | None -> Chunk.empty
  in
  let stmts = decl_stmt @ init_stmt.stmts @ cond_sl @ if_chunk.Chunk.stmts in
  let cases = init_stmt.cases @ then_stmt.cases @ else_stmt.cases in
  ( {
      Chunk.stmts;
      cases;
      labels = if_chunk.labels;
      gotos = if_chunk.gotos;
      user_typs = init_stmt.user_typs;
    },
    scope )

and trans_block scope fundec body =
  match body.C.Ast.desc with
  | C.Ast.Compound l -> trans_compound scope fundec l |> fst
  | _ -> trans_stmt scope fundec body |> fst

and trans_switch scope fundec loc init cond_var cond body =
  let init, _ = trans_stmt_opt scope fundec init in
  let decl_sl, scope = trans_var_decl_opt scope fundec loc cond_var in
  let cond_sl, cond_expr_opt = trans_expr scope (Some fundec) loc AExp cond in
  let cond_expr = Option.get cond_expr_opt in
  let body_stmt = trans_stmt scope fundec body |> fst in
  let body = { Cil.battrs = []; bstmts = body_stmt.Chunk.stmts } in
  let cases =
    List.fold_left
      (fun acc s -> if List.memq s acc then acc else s :: acc)
      []
      (init.cases @ body_stmt.cases)
    |> List.rev
  in
  let stmts =
    init.Chunk.stmts @ decl_sl @ cond_sl
    @ [ Cil.mkStmt (Cil.Switch (cond_expr, body, cases, loc)) ]
  in
  ( {
      Chunk.stmts;
      cases = body_stmt.cases;
      labels = body_stmt.labels;
      gotos = body_stmt.gotos;
      user_typs = body_stmt.user_typs;
    },
    scope )

and trans_case scope fundec loc lhs body =
  let lhs_expr = trans_expr scope (Some fundec) loc ADrop lhs |> snd in
  let chunk = trans_stmt scope fundec body |> fst in
  let label = Cil.Case (Option.get lhs_expr, loc) in
  match chunk.Chunk.stmts with
  | h :: _ ->
      h.labels <- h.labels @ [ label ];
      ({ chunk with cases = h :: chunk.cases }, scope)
  | [] -> (chunk, scope)

and trans_default scope fundec loc stmt =
  let chunk = trans_stmt scope fundec stmt |> fst in
  let label = Cil.Default loc in
  match chunk.Chunk.stmts with
  | h :: _ ->
      h.labels <- label :: h.labels;
      ({ chunk with cases = chunk.cases @ [ h ] }, scope)
  | [] -> (chunk, scope)

and trans_label scope fundec loc label body =
  (* Clang frontend guarantees the uniqueness of label names,
   * so do not need to create unique names.
   * Instead, we only add the label name to the scope,
   * to avoid conflicts with CIL-generated label names *)
  let scope = Scope.add_label label scope in
  let chunk = trans_stmt scope fundec body |> fst in
  (append_label chunk label loc true, scope)

and trans_stmt_opt scope fundec = function
  | Some s -> trans_stmt scope fundec s
  | None -> (Chunk.empty, scope)

and trans_global_decl ?(new_name = "") scope (decl : C.Ast.decl) =
  let loc = trans_location decl in
  let storage = trans_storage decl in
  match decl.desc with
  | C.Ast.Function fdecl when fdecl.body = None ->
      let name = string_of_declaration_name fdecl.name in
      let typ = Cil.TFun (Cil.voidType, None, false, []) in
      let svar, scope = find_global_variable scope name typ in
      let scope = Scope.enter_function scope in
      let typ, scope =
        trans_function_type scope None fdecl.C.Ast.function_type
      in
      svar.vtype <- typ;
      svar.vstorage <- storage;
      svar.vattr <- trans_decl_attribute fdecl.attributes;
      let scope = Scope.exit_function scope in
      ([ Cil.GVarDecl (svar, loc) ], scope)
  | C.Ast.Function fdecl ->
      let name = string_of_declaration_name fdecl.name in
      let fundec = Cil.emptyFunction name in
      let typ = Cil.TFun (Cil.voidType, None, false, []) in
      let svar, scope = find_global_variable scope name typ in
      let scope = Scope.enter_function scope in
      let typ, scope =
        trans_function_type scope (Some fundec) fdecl.C.Ast.function_type
      in
      fundec.svar <- svar;
      fundec.svar.vtype <- typ;
      fundec.svar.vstorage <- storage;
      fundec.svar.vattr <- trans_decl_attribute fdecl.attributes;
      fundec.svar.vinline <-
        C.Ast.cursor_of_node decl |> C.cursor_is_function_inlined;
      let fun_body = trans_function_body scope fundec (Option.get fdecl.body) in
      fundec.sbody <- fst fun_body;
      let scope = Scope.exit_function scope in
      CilHelper.insert_missing_return fundec;
      (snd fun_body @ [ Cil.GFun (fundec, loc) ], scope)
  | C.Ast.Var vdecl when vdecl.var_init = None ->
      let typ = trans_type scope vdecl.var_type in
      let vi, scope = find_global_variable scope vdecl.var_name typ in
      vi.vstorage <- storage;
      ([ Cil.GVarDecl (vi, loc) ], scope)
  | C.Ast.Var vdecl ->
      let typ = trans_type scope vdecl.var_type in
      let vi, scope = find_global_variable scope vdecl.var_name typ in
      vi.vstorage <- storage;
      let e = Option.get vdecl.var_init in
      let init = Some (trans_global_init scope loc typ e) in
      vi.vinit.init <- init;
      ([ Cil.GVar (vi, { Cil.init }, loc) ], scope)
  | C.Ast.RecordDecl rdecl when rdecl.C.Ast.complete_definition ->
      let is_struct = rdecl.keyword = C.Struct in
      let globals, scope =
        List.fold_left
          (fun (globals, scope) decl ->
            let gs, scope = trans_global_decl scope decl in
            (globals @ gs, scope))
          ([], scope) rdecl.fields
      in
      let callback compinfo =
        List.fold_left
          (fun fl (decl : C.Ast.decl) ->
            match decl.C.Ast.desc with
            | C.Ast.Field _ -> fl @ [ trans_field_decl scope compinfo decl ]
            | C.Ast.IndirectField _ ->
                fl @ trans_indirect_field_decl scope compinfo decl
            | _ -> fl)
          [] rdecl.fields
      in
      let cursor = C.Ast.cursor_of_decoration decl.decoration in
      let name =
        if new_name = "" then new_record_id is_struct rdecl cursor |> fst
        else new_name
      in
      let compinfo = Cil.mkCompInfo is_struct name callback [] in
      compinfo.cdefined <- true;
      if Scope.mem_comp name scope then (
        let typ = Scope.find_comp name scope in
        let prev_ci = get_compinfo typ in
        prev_ci.cfields <- compinfo.cfields;
        (globals @ [ Cil.GCompTag (prev_ci, loc) ], scope))
      else
        let typ = Cil.TComp (compinfo, []) in
        let scope = Scope.add_comp name typ scope in
        (globals @ [ Cil.GCompTag (compinfo, loc) ], scope)
  | C.Ast.RecordDecl rdecl ->
      let is_struct = rdecl.keyword = C.Struct in
      let cursor = C.Ast.cursor_of_decoration decl.decoration in
      let name =
        if new_name = "" then new_record_id is_struct rdecl cursor |> fst
        else new_name
      in
      if Scope.mem_comp name scope then
        let typ = Scope.find_comp name scope in
        let prev_ci = get_compinfo typ in
        ([ Cil.GCompTagDecl (prev_ci, loc) ], scope)
      else
        let callback _ = [] in
        let compinfo = Cil.mkCompInfo is_struct name callback [] in
        let typ = Cil.TComp (compinfo, []) in
        let scope = Scope.add_comp rdecl.name typ scope in
        ([ Cil.GCompTagDecl (compinfo, loc) ], scope)
  | TypedefDecl tdecl ->
      let ttype = trans_type scope tdecl.underlying_type in
      let tinfo = { Cil.tname = tdecl.name; ttype; treferenced = false } in
      let scope = Scope.add_type tdecl.name (Cil.TNamed (tinfo, [])) scope in
      ([ Cil.GType (tinfo, loc) ], scope)
  | EnumDecl edecl ->
      let eitems, scope, _ =
        List.fold_left
          (fun (eitems, scope, next) (c : C.Ast.enum_constant) ->
            let value = C.Enum_constant.get_value c |> Cil.integer in
            let scope =
              Scope.add c.desc.constant_name (EnvData.EnvEnum value) scope
            in
            (eitems @ [ (c.desc.constant_name, value, loc) ], scope, next))
          ([], scope, Cil.zero) edecl.constants
      in
      let name =
        if new_name = "" then
          if edecl.name = "" then new_enum_id "" else edecl.name
        else new_name
      in
      let einfo =
        {
          Cil.ename = name;
          eitems;
          eattr = [];
          ereferenced = false;
          ekind = Cil.IInt;
        }
      in
      let scope = Scope.add_type edecl.name (Cil.TEnum (einfo, [])) scope in
      ([ Cil.GEnumTag (einfo, loc) ], scope)
  | Field _ | IndirectField _ | EmptyDecl | AccessSpecifier _ | Namespace _
  | UsingDirective _ | UsingDeclaration _ | Constructor _ | Destructor _
  | LinkageSpec _ | TemplateTemplateParameter _ | Friend _ | NamespaceAlias _
  | Directive _ | StaticAssert _ | TypeAlias _ | Decomposition _
  | UnknownDecl (_, _) ->
      ([], scope)
  | TemplateDecl _ | TemplatePartialSpecialization _ | CXXMethod _ ->
      failwith "Unsupported C++ features"
  | Concept _ | Export _ -> failwith "new cases: Concept | Export"

and trans_function_body scope fundec body =
  let chunk = trans_block scope fundec body in
  let vis = new replaceGotoVisitor chunk.Chunk.gotos chunk.Chunk.labels in
  ( {
      Cil.battrs = [];
      bstmts = List.map (Cil.visitCilStmt vis) chunk.Chunk.stmts;
    },
    chunk.user_typs )

and mk_init scope loc fitype expr_list =
  (* for uninitaiized *)
  match (Cil.unrollType fitype, expr_list) with
  | Cil.TInt (ikind, _), [] -> (Cil.SingleInit (Cil.kinteger ikind 0), [])
  | Cil.TFloat (fkind, _), [] ->
      (Cil.SingleInit (Cil.Const (Cil.CReal (0., fkind, None))), [])
  | Cil.TPtr (typ, _), [] ->
      (Cil.SingleInit (Cil.CastE (TPtr (typ, []), Cil.integer 0)), [])
  | Cil.TEnum (_, _), [] -> (Cil.SingleInit (Cil.integer 0), [])
  (* for initaiized *)
  | Cil.TInt (_, _), e :: el ->
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, el)
  | Cil.TFloat (_, _), e :: el ->
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, el)
  | Cil.TPtr (_, _), e :: el ->
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, el)
  (* common *)
  | Cil.TComp (ci, _), _ ->
      (* struct in struct *)
      mk_global_struct_init scope loc fitype ci.cfields expr_list
  | Cil.TArray (arr_type, arr_exp, _), _ ->
      let len_exp = Option.get arr_exp in
      let arr_len =
        match len_exp with
        | Const c -> (
            match c with
            | CInt64 (v, _, _) -> Int64.to_int v
            | _ -> failwith "not expected")
        | _ -> failwith "not expected"
      in
      let final_init =
        let inits, expr_remainders, _ =
          List.init arr_len id
          |> List.fold_left
               (fun (inits, expr_remainders, o) _ ->
                 match Cil.unrollType arr_type with
                 | Cil.TComp (ci, _) ->
                     let init, expr_remainders' =
                       mk_global_struct_init scope loc fitype ci.cfields
                         expr_remainders
                     in
                     let init_with_idx =
                       (Cil.Index (Cil.integer o, Cil.NoOffset), init)
                     in
                     (init_with_idx :: inits, expr_remainders', o + 1)
                 | _ ->
                     if expr_list <> [] && expr_remainders <> [] then
                       let e = List.hd expr_remainders in
                       let _, expr_opt = trans_expr scope None loc ADrop e in
                       let e = Option.get expr_opt in
                       let init = Cil.SingleInit e in
                       let init_with_idx =
                         (Cil.Index (Cil.integer o, Cil.NoOffset), init)
                       in
                       (init_with_idx :: inits, List.tl expr_remainders, o + 1)
                     else
                       let init =
                         Cil.SingleInit (Cil.CastE (arr_type, Cil.integer 0))
                       in
                       let init_with_idx =
                         (Cil.Index (Cil.integer o, Cil.NoOffset), init)
                       in
                       (init_with_idx :: inits, expr_remainders, o + 1))
               ([], expr_list, 0)
        in
        (Cil.CompoundInit (fitype, List.rev inits), expr_remainders)
      in
      final_init
  | Cil.TEnum (_, _), e :: el ->
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, el)
  | _ -> failwith "not expected"

and mk_global_struct_init scope loc typ cfields expr_list =
  let origin_cfields = cfields in
  let rec loop union_flag cfields expr_list fis inits idx_list idx =
    match (cfields, expr_list) with
    | f :: fl, e :: el ->
        if union_flag then
          loop union_flag fl expr_list fis inits ((idx + 1) :: idx_list)
            (idx + 1)
        else if f.Cil.fcomp.cstruct then
          if is_init_list e then
            let init = trans_global_init scope loc f.ftype e in
            loop union_flag fl el (f :: fis) (init :: inits)
              ((idx + 1) :: idx_list) (idx + 1)
          else
            let field, find, i = grab_matching_field origin_cfields f e in
            let f = List.hd field in
            let i = if i >= 0 then find else idx + 1 in
            let expr_list =
              if i >= 0 then
                match expr_list with
                | e :: el -> (
                    match e.C.Ast.desc with
                    | C.Ast.DesignatedInit d -> d.init :: el
                    | _ -> expr_list)
                | _ -> expr_list
              else expr_list
            in
            let init, expr_remainders =
              mk_init scope loc f.Cil.ftype expr_list
            in
            loop union_flag fl expr_remainders (f :: fis) (init :: inits)
              (i :: idx_list) (idx + 1)
        else if is_init_list e then
          let init = trans_global_init scope loc f.ftype e in
          loop true fl el (f :: fis) (init :: inits) ((idx + 1) :: idx_list)
            (idx + 1)
        else
          let _, expr_opt = trans_expr scope None loc ADrop e in
          let e = Option.get expr_opt in
          let init = Cil.SingleInit e in
          loop true fl el (f :: fis) (init :: inits) ((idx + 1) :: idx_list)
            (idx + 1)
    | f :: fl, [] ->
        if union_flag then
          loop union_flag fl [] fis inits ((idx + 1) :: idx_list) (idx + 1)
        else if f.fcomp.cstruct then
          let init, _ = mk_init scope loc f.Cil.ftype [] in
          loop union_flag fl [] (f :: fis) (init :: inits)
            ((idx + 1) :: idx_list) (idx + 1)
        else
          let init = Cil.SingleInit (Cil.integer 0) in
          loop true fl [] (f :: fis) (init :: inits) ((idx + 1) :: idx_list)
            (idx + 1)
    | [], _ -> (fis, inits, expr_list, idx_list, idx)
  in
  let fis, inits, expr_list, idx_list, _ =
    loop false cfields expr_list [] [] [] 0
  in
  let inits =
    if List.length inits = List.length idx_list then
      sort_list_with_index inits idx_list
    else inits
  in
  let inits =
    List.fold_left2
      (fun fields_offset fi init ->
        (Cil.Field (fi, Cil.NoOffset), init) :: fields_offset)
      [] fis inits
  in
  (Cil.CompoundInit (typ, inits), expr_list)

and trans_global_init scope loc typ (e : C.Ast.expr) =
  match (e.C.Ast.desc, Cil.unrollType typ) with
  | C.Ast.InitList el, Cil.TArray (elt_typ, None, _) ->
      let init_list =
        List.fold_left
          (fun (r, o) i ->
            let init = trans_global_init scope loc elt_typ i in
            ((Cil.Index (Cil.integer o, Cil.NoOffset), init) :: r, o + 1))
          ([], 0) el
        |> fst |> List.rev
      in
      Cil.CompoundInit (typ, init_list)
  | C.Ast.InitList el, Cil.TArray (elt_typ, Some len_exp, _) ->
      let arr_len =
        match len_exp with
        | Const c -> (
            match c with
            | CInt64 (v, _, _) -> Int64.to_int v
            | _ -> failwith "not expected")
        | _ -> failwith "not expected"
      in
      let el =
        if List.length el > arr_len then BatList.take arr_len el else el
      in
      let init_list =
        List.fold_left
          (fun (r, o) i ->
            let init = trans_global_init scope loc elt_typ i in
            ((Cil.Index (Cil.integer o, Cil.NoOffset), init) :: r, o + 1))
          ([], 0) el
        |> fst |> List.rev
      in
      Cil.CompoundInit (typ, init_list)
  | C.Ast.InitList el, Cil.TComp (ci, _) ->
      mk_global_struct_init scope loc typ ci.cfields el |> fst
  | C.Ast.InitList el, _ when el <> [] ->
      (* accept only first scalar and ignore remainder *)
      List.hd el |> trans_expr scope None loc ADrop |> snd |> Option.get
      |> fun x -> Cil.SingleInit x
  | _ ->
      trans_expr scope None loc ADrop e |> snd |> Option.get |> fun x ->
      Cil.SingleInit x

let initialize_builtins scope =
  H.fold
    (fun name (rtyp, argtyps, isva) scope ->
      let argtyps = Some (List.map (fun at -> ("", at, [])) argtyps) in
      create_new_global_variable scope name (Cil.TFun (rtyp, argtyps, isva, []))
      |> snd)
    Cil.builtinFunctions scope

let split_decl (items : C.Ast.decl list) =
  List.partition
    (fun (decl : C.Ast.decl) ->
      match decl.C.Ast.desc with
      | C.Ast.Function _ -> false
      | C.Ast.Var _ -> false
      | _ -> true)
    items

let parse fname =
  let index =
    C.create_index ~exclude_declarations_from_pch:false
      ~display_diagnostics:false
  in
  let options =
    {
      C.Ast.Options.default with
      ignore_implicit_cast = false;
      ignore_indirect_fields = false;
      ignore_anonymous_fields = false;
    }
  in
  L.debug "Loading %s\n" fname;
  if !Options.debug then L.flush_all ();
  let tu : C.Ast.translation_unit =
    StepManager.stepf ~to_consol:false false ("Parsing " ^ fname)
      (C.Ast.parse_file ~index ~options)
      fname
  in
  let scope = initialize_builtins (Scope.create ()) in
  let desc = tu.desc in
  (* to make it consistent with CIL, translate types first, vars next *)
  let types, vars = split_decl desc.items in
  let globals =
    List.fold_left
      (fun (globals, scope) decl ->
        let new_globals, scope = trans_global_decl scope decl in
        (List.rev_append new_globals globals, scope))
      ([], scope) (types @ vars)
    |> fst |> List.rev
  in
  let cil =
    {
      Cil.fileName = fname;
      Cil.globals;
      Cil.globinit = None;
      Cil.globinitcalled = false;
    }
  in
  (* the below is a temporal workaround for clangml's strange behavior *)
  let target =
    Filename.concat
      (Filename.concat !Options.outdir "preprocess")
      (Filename.basename fname ^ ".bin")
  in
  let oc = open_out target in
  Marshal.to_channel oc cil [];
  close_out oc
