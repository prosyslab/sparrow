open Vocab
module H = Hashtbl
module C = Claml.Clang
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
  type t = (string, string) H.t

  let create () = H.create 64

  let add_label name env =
    H.add env name name;
    env

  let mem_label name env = H.mem env name

  let find_label name env = H.find env name
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

  let exit_block scope = match scope with bs, fs -> (List.tl bs, fs)

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

let is_init_list expr =
  match C.Expr.get_kind expr with C.StmtKind.InitListExpr -> true | _ -> false

let anonymous_id_table = H.create 1024

let new_record_id is_struct rdecl =
  let name = C.RecordDecl.get_name rdecl in
  if name = "" then (
    let h = C.RecordDecl.get_global_id rdecl in
    if H.mem anonymous_id_table h then (H.find anonymous_id_table h, false)
    else
      let kind = if is_struct then "struct" else "union" in
      let name = "__anon" ^ kind ^ "_" ^ string_of_int !struct_id_count in
      struct_id_count := !struct_id_count + 1;
      H.add anonymous_id_table h name;
      (name, true))
  else (name, false)

let new_enum_id edecl =
  let name = C.EnumDecl.get_name edecl in
  if name = "" then (
    let h = C.EnumDecl.get_global_id edecl in
    if H.mem anonymous_id_table h then (H.find anonymous_id_table h, false)
    else
      let name = "__anonenum_" ^ name ^ "_" ^ string_of_int !struct_id_count in
      struct_id_count := !struct_id_count + 1;
      H.add anonymous_id_table h name;
      (name, true))
  else (name, false)

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

let rec create_label scope label =
  let new_name =
    if Scope.mem_label label scope then (
      let new_name = label ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name)
    else label
  in
  if Scope.mem_label new_name scope then create_label scope label
  else
    let scope = Scope.add_label new_name scope in
    (new_name, scope)

let trans_location loc =
  match loc with
  | Some location ->
      {
        Cil.file = location.C.SourceLocation.filename;
        line = location.C.SourceLocation.line;
        byte = location.column;
      }
  | None -> { Cil.file = ""; line = -1; byte = -1 }

let get_compinfo typ =
  match Cil.unrollType typ with
  | Cil.TComp (ci, _) -> ci
  | _ -> failwith ("invalid type: " ^ CilHelper.s_type typ)

let trans_int_kind = function
  | C.BuiltinTypeKind.Int | Bool | Int128 -> Cil.IInt
  | Char_U | UChar -> Cil.IUChar
  | UShort -> Cil.IUShort
  | UInt | UInt128 -> Cil.IUInt
  | ULong -> Cil.IULong
  | ULongLong -> Cil.IULongLong
  | Char_S -> Cil.IChar
  | SChar -> Cil.ISChar
  | Short -> Cil.IShort
  | Long -> Cil.ILong
  | LongLong -> Cil.ILongLong
  | _ -> invalid_arg "int kind"

let trans_float_kind = function
  | C.BuiltinTypeKind.Float -> Cil.FFloat
  | Double -> Cil.FDouble
  | LongDouble -> Cil.FLongDouble
  | _ -> invalid_arg "float kind"

let trans_binop lhs rhs = function
  | C.BinaryOperatorKind.Mul -> Cil.Mult
  | Div -> Cil.Div
  | Rem -> Cil.Mod
  | Add when Cil.typeOf lhs |> Cil.isPointerType -> Cil.PlusPI
  | Add -> Cil.PlusA
  | Sub
    when Cil.typeOf lhs |> Cil.isPointerType
         && Cil.typeOf rhs |> Cil.isPointerType ->
      Cil.MinusPP
  | Sub when Cil.typeOf lhs |> Cil.isPointerType -> Cil.MinusPI
  | Sub -> Cil.MinusA
  | Shl -> Cil.Shiftlt
  | Shr -> Cil.Shiftrt
  | LT -> Cil.Lt
  | GT -> Cil.Gt
  | LE -> Cil.Le
  | GE -> Cil.Ge
  | EQ -> Cil.Eq
  | NE -> Cil.Ne
  | And -> Cil.BAnd
  | Xor -> Cil.BXor
  | Or -> Cil.BOr
  | LAnd -> Cil.LAnd
  | LOr -> Cil.LOr
  | _ -> failwith "invalid binop"

let const_attribute = [ Cil.Attr ("const", []) ]

let trans_attribute typ = if typ.C.QualType.const then const_attribute else []

let failwith_decl decl = failwith (C.Decl.get_kind_name decl)

let trans_integer_literal il =
  let ikind =
    let qt = C.IntegerLiteral.get_type il in
    match C.Type.get_kind qt.C.QualType.ty with
    | C.TypeKind.BuiltinType -> C.BuiltinType.get_kind qt.ty |> trans_int_kind
    | _ -> failwith "Invalid type for integer literal"
  in
  C.IntegerLiteral.to_int il |> Int64.to_int |> Cil.kinteger ikind

let trans_floating_literal il =
  let fkind =
    let qt = C.FloatingLiteral.get_type il in
    match C.Type.get_kind qt.C.QualType.ty with
    | C.TypeKind.BuiltinType -> C.BuiltinType.get_kind qt.ty |> trans_float_kind
    | _ -> failwith "Invalid type for float literal"
  in
  let f = C.FloatingLiteral.to_float il in
  Cil.Const (Cil.CReal (f, fkind, None))

let trans_string_literal sl =
  Cil.Const (Cil.CStr (C.StringLiteral.get_string sl))

let trans_decl_ref scope allow_undef idref =
  let name = C.DeclRefExpr.get_decl idref |> C.NamedDecl.get_name in
  match Scope.find_var_enum ~allow_undef name scope with
  | EnvVar varinfo ->
      let exp = Cil.Lval (Cil.Var varinfo, NoOffset) in
      ([], Some exp)
  | EnvEnum enum -> ([], Some enum)
  | _ -> failwith "no found"

let grab_matching_field cfields f expr =
  List.fold_left
    (fun (fi', find, idx) fi ->
      let fi'', find, idx =
        match C.Expr.get_kind expr with
        | C.StmtKind.DesignatedInitExpr ->
            C.DesignatedInitExpr.get_designators expr
            |> List.fold_left
                 (fun (fi', find, idx) designator ->
                   if C.Designator.is_field_designator designator then
                     if C.Designator.get_field_name designator = fi.Cil.fname
                     then ([ fi ], idx, idx)
                     else (fi', find, idx)
                   else if C.Designator.is_array_designator designator then
                     (fi', find, idx)
                   else (fi', find, idx))
                 (fi', find, idx)
        | _ -> if fi' <> [] then (fi', find, idx) else ([ f ], find, -10000)
      in
      (fi'', find, idx + 1))
    ([], 0, 0) cfields

let sort_list_with_index data_list idx_list =
  List.combine data_list idx_list
  |> List.sort (fun (_, idx1) (_, idx2) -> if idx1 > idx2 then 1 else 0)
  |> List.split |> fst |> List.rev

let should_ignore_implicit_cast ?(is_ignore_fun_ptr_decay = true) expr qual_type
    e typ =
  match (C.CastExpr.get_kind expr, e) with
  | C.ImplicitCastKind.FunctionToPointerDecay, _ | BuiltinFnToFnPtr, _ ->
      is_ignore_fun_ptr_decay
  | LValueToRValue, _ | BitCast, _ -> true
  | ArrayToPointerDecay, Cil.Const (Cil.CStr _) -> true
  | _, _ ->
      (* TODO: cleanup *)
      let expr_kind = C.Expr.get_kind expr in
      let type_kind = C.Type.get_kind qual_type.C.QualType.ty in
      (* ignore FunctionToPointerDecay and BuiltinFnToFnPtr *)
      (expr_kind = C.StmtKind.ImplicitCastExpr
       && type_kind = C.TypeKind.FunctionNoProtoType
      || type_kind = C.TypeKind.FunctionProtoType)
      && is_ignore_fun_ptr_decay
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

let get_opt msg = function Some x -> x | None -> failwith msg

let goto_count = ref 0

module Chunk = struct
  module LabelMap = struct
    include Map.Make (String)

    let pp_keys fmt m = iter (fun k _ -> F.fprintf fmt "%s\n" k) m

    let append xm ym =
      union
        (fun x _ _ ->
          F.fprintf F.std_formatter "1st LabelMap keys:\n%a" pp_keys xm;
          F.fprintf F.std_formatter "2nd LabelMap keys:\n%a" pp_keys ym;
          failwith ("duplicated labels: " ^ x))
        xm ym
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
  | [] ->
      let h = Cil.mkStmt (Cil.Instr []) in
      h.labels <- [ l ];
      {
        chunk with
        stmts = [ h ];
        labels = Chunk.LabelMap.add label (ref h) chunk.labels;
      }

let trans_storage decl =
  match C.Decl.get_storage_class decl with
  | C.Decl.Extern -> Cil.Extern
  | C.Decl.Register -> Cil.Register
  | C.Decl.Static -> Cil.Static
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
    (fun attrs attr ->
      match C.Attr.get_kind attr with
      | C.AttrKind.GNUInline -> att_gnu_inline :: attrs
      | C.AttrKind.NoThrow -> att_nothrow :: attrs
      | _ -> attrs)
    [] attrs

let get_stmt_lst stmt =
  match C.Stmt.get_kind stmt with
  | C.StmtKind.CompoundStmt -> C.CompoundStmt.body_list stmt
  | _ -> [ stmt ]

let get_opt_stmt_lst stmt_opt =
  match stmt_opt with Some s -> get_stmt_lst s | None -> []

let rec add_labels scope sl =
  let sc', new_sl =
    List.fold_left
      (fun (s', sls') stmt ->
        match C.Stmt.get_kind stmt with
        | C.StmtKind.LabelStmt ->
            ( Scope.add_label (C.LabelStmt.get_name stmt) s',
              get_stmt_lst (C.LabelStmt.get_sub_stmt stmt) @ sls' )
        | CompoundStmt -> (s', C.CompoundStmt.body_list stmt @ sls')
        | IfStmt ->
            let tb = C.IfStmt.get_then stmt |> get_stmt_lst in
            let fb =
              if C.IfStmt.has_else_storage stmt then
                C.IfStmt.get_else stmt |> Option.get |> get_stmt_lst
              else []
            in
            (s', tb @ fb @ sls')
        | ForStmt -> (s', (C.ForStmt.get_body stmt |> get_stmt_lst) @ sls')
        | WhileStmt -> (s', (C.WhileStmt.get_body stmt |> get_stmt_lst) @ sls')
        | DoStmt -> (s', (C.DoStmt.get_body stmt |> get_stmt_lst) @ sls')
        | _ -> (s', sls'))
      (scope, []) sl
  in
  if new_sl = [] then sc' else add_labels sc' new_sl

let rec trans_type ?(compinfo = None) scope typ =
  (*   F.eprintf "==%a\n==" C.QualType.pp typ; *)
  match C.Type.get_kind typ.C.QualType.ty with
  | C.TypeKind.PointerType -> (
      try
        let t = C.PointerType.get_pointee_type typ.ty in
        Cil.TPtr (trans_type ~compinfo scope t, trans_attribute typ)
      with _ ->
        (* TODO: https://github.com/prosyslab/sparrow/issues/28 *)
        L.warn ~to_consol:false "WARN: type not found\n";
        Cil.voidPtrType)
  | ParenType -> C.ParenType.desugar typ.ty |> trans_type ~compinfo scope
  | FunctionProtoType | FunctionNoProtoType ->
      trans_function_type scope None None typ |> fst
  | TypedefType ->
      let tname = C.TypedefType.get_decl typ.ty |> C.TypedefDecl.get_name in
      Scope.find_type tname scope
  | ElaboratedType ->
      C.ElaboratedType.desugar typ.ty |> trans_type ~compinfo scope
  | RecordType ->
      let decl = C.RecordType.get_decl typ.ty in
      let name = C.RecordDecl.get_name decl in
      let name, scope =
        if name = "" then
          let is_struct = C.RecordDecl.is_struct decl in
          let name, is_new_anon = new_record_id is_struct decl in
          let fields = C.RecordDecl.field_list decl in
          let callback compinfo =
            List.fold_left
              (fun fl decl ->
                match C.Decl.get_kind decl with
                | FieldDecl -> fl @ [ trans_field_decl scope compinfo decl ]
                | IndirectFieldDecl ->
                    fl @ trans_indirect_field_decl scope compinfo decl
                | _ -> fl)
              [] fields
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
  | EnumType ->
      let decl = C.EnumType.get_decl typ.ty in
      let name = C.EnumDecl.get_name decl in
      let name = if name = "" then new_enum_id decl |> fst else name in
      Scope.find_type name scope
  (* | InvalidType ->
         L.warn ~to_consol:false "WARN: invalid type (use int instead)\n";
         Cil.intType
     | Vector vt ->
         let size = Cil.integer vt.size in
         let elem_type = trans_type ~compinfo scope vt.element in
         let attr = trans_attribute typ in
         Cil.TArray (elem_type, Some size, attr)
  *)
  | BuiltinType -> trans_builtin_type typ
  | ConstantArrayType ->
      let size =
        C.ConstantArrayType.get_size typ.ty |> Int64.to_int |> Cil.integer
      in
      let elem_type =
        C.ConstantArrayType.get_element_type typ.ty
        |> trans_type ~compinfo scope
      in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, Some size, attr)
  | IncompleteArrayType ->
      let elem_type =
        C.IncompleteArrayType.get_element_type typ.ty
        |> trans_type ~compinfo scope
      in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, None, attr)
  | VariableArrayType ->
      let size = C.VariableArrayType.get_size_expr typ.ty in
      let _, size = trans_expr scope None Cil.locUnknown AExp size in
      let elem_type =
        C.VariableArrayType.get_element_type typ.ty
        |> trans_type ~compinfo scope
      in
      let attr = trans_attribute typ in
      Cil.TArray (elem_type, Some (Option.get size), attr)
  | TypeOfExprType ->
      C.TypeOfExprType.get_underlying_expr typ.ty
      |> C.Expr.get_type |> trans_type ~compinfo scope
  | DecayedType ->
      C.DecayedType.get_original_type typ.ty |> trans_type ~compinfo scope
  | AdjustedType ->
      C.AdjustedType.get_original_type typ.ty |> trans_type ~compinfo scope
  | UnaryTransformType -> failwith "qwer"
  | _ -> failwith ("Unknown type " ^ C.Type.get_kind_name typ.ty)

and trans_builtin_type t =
  let k = C.BuiltinType.get_kind t.C.QualType.ty in
  let attr = trans_attribute t in
  match k with
  | Void -> Cil.TVoid attr
  (* integer types *)
  | Int | Bool | Char_U | UChar | UShort | UInt | ULong | ULongLong | Char_S
  | SChar | Short | Long | LongLong | Int128 | UInt128 ->
      Cil.TInt (trans_int_kind k, attr)
  | Float | Double | LongDouble -> Cil.TFloat (trans_float_kind k, attr)
  | _ ->
      F.fprintf F.err_formatter "%a\n" C.BuiltinType.pp t.ty;
      F.pp_print_flush F.err_formatter ();
      failwith "trans_builtin_type"

and trans_function_type scope fundec_opt decl_opt typ =
  let ty = typ.C.QualType.ty in
  let rec is_function_type_variadic typ =
    match C.Type.get_kind typ.C.QualType.ty with
    | C.TypeKind.FunctionProtoType -> C.FunctionProtoType.is_variadic typ.ty
    | C.TypeKind.FunctionNoProtoType -> false
    | C.TypeKind.TypedefType ->
        C.TypedefType.get_decl typ.ty
        |> C.TypedefDecl.get_underlying_type |> is_function_type_variadic
    | C.TypeKind.ParenType ->
        C.ParenType.desugar typ.ty |> is_function_type_variadic
    | _ ->
        F.fprintf F.err_formatter "%a (%s)\n" C.QualType.pp typ
          (C.Type.get_kind_name typ.ty);
        assert false
  in
  let return_typ =
    match decl_opt with
    | Some decl ->
        let rt = C.FunctionDecl.get_return_type decl in
        trans_type scope rt
    | _ -> trans_type scope (C.FunctionType.return_type typ.C.QualType.ty)
  in
  let is_variadic = is_function_type_variadic typ in
  let param_types, var_arg, scope =
    match decl_opt with
    | Some decl ->
        trans_parameter_types_with_decls scope fundec_opt
          (C.FunctionDecl.get_params decl)
          is_variadic
    | None ->
        trans_parameter_types_without_decls scope
          (C.FunctionType.param_types ty)
          is_variadic
  in
  (Cil.TFun (return_typ, param_types, var_arg, []), scope)

and trans_parameter_types_with_decls scope fundec_opt params is_variadic =
  match params with
  | [] -> (None, false, scope)
  | _ ->
      let scope, formals =
        List.fold_left
          (fun (scope, formals) param ->
            let param_typ = trans_type scope (C.ParmVarDecl.get_type param) in
            let name = C.ParmVarDecl.get_name param in
            let result = (name, param_typ, []) in
            if name = "" then (scope, result :: formals)
            else
              let make_var =
                match fundec_opt with
                | Some fundec -> fun n t -> Cil.makeFormalVar fundec n t
                | None -> fun n t -> Cil.makeVarinfo false n t
              in
              let vi = make_var name param_typ in
              let scope = Scope.add name (EnvData.EnvVar vi) scope in
              (scope, result :: formals))
          (scope, []) params
      in
      (List.rev formals |> Option.some, is_variadic, scope)

and trans_parameter_types_without_decls scope param_types is_variadic =
  match param_types with
  | [] -> (None, false, scope)
  | _ ->
      let scope, formals =
        List.fold_left
          (fun (scope, formals) param ->
            let param_typ = trans_type scope param in
            let name = "" in
            let result = (name, param_typ, []) in
            (scope, result :: formals))
          (scope, []) param_types
      in
      (List.rev formals |> Option.some, is_variadic, scope)

and trans_field_decl scope compinfo field =
  let floc = C.Decl.get_source_location field |> trans_location in
  match C.Decl.get_kind field with
  | C.DeclKind.FieldDecl ->
      let typ =
        C.FieldDecl.get_type field |> trans_type ~compinfo:(Some compinfo) scope
      in
      (C.FieldDecl.get_name field, typ, None, [], floc)
  | _ -> failwith_decl field

and trans_indirect_field_decl scope compinfo ifdecl =
  match C.Decl.get_kind ifdecl with
  | C.DeclKind.IndirectFieldDecl ->
      (* IndirectField consists of several FieldDecls.
         Some of them are anonymous field whose name is '',
         and the rest are named fields.
         Only named fields are required to be embedded.*)
      let named_decls =
        C.IndirectFieldDecl.get_decl_list ifdecl
        |> List.fold_left
             (fun ndecls fdecl ->
               match C.Decl.get_kind fdecl with
               | C.DeclKind.FieldDecl ->
                   if C.FieldDecl.get_name fdecl <> "" then fdecl :: ndecls
                   else ndecls
               | _ -> failwith_decl fdecl)
             []
      in
      List.fold_left
        (fun res ndecl -> res @ [ trans_field_decl scope compinfo ndecl ])
        [] named_decls
  | _ -> failwith_decl ifdecl

(* In case of failure, produce 0 if default_ptr is false, a temp var if true *)
and trans_expr ?(allow_undef = false) ?(skip_lhs = false) ?(default_ptr = false)
    ?(is_ignore_fun_ptr_decay = true) scope fundec_opt loc action expr =
  match C.Expr.get_kind expr with
  | C.StmtKind.IntegerLiteral -> ([], Some (trans_integer_literal expr))
  | FloatingLiteral -> ([], Some (trans_floating_literal expr))
  | StringLiteral -> ([], Some (trans_string_literal expr))
  | CharacterLiteral ->
      let v = C.CharacterLiteral.get_value expr in
      if v > 255 then ([], Some (Cil.kinteger Cil.IUInt v))
      else ([], Some (Cil.Const (Cil.CChr (char_of_int v))))
  | UnaryOperator ->
      let kind = C.UnaryOperator.get_kind expr in
      let operand = C.UnaryOperator.get_sub_expr expr in
      trans_unary_operator scope fundec_opt loc action kind operand
  | BinaryOperator | CompoundAssignOperator ->
      let kind = C.BinaryOperator.get_kind expr in
      let lhs = C.BinaryOperator.get_lhs expr in
      let rhs = C.BinaryOperator.get_rhs expr in
      trans_binary_operator scope fundec_opt loc kind lhs rhs
  | DeclRefExpr -> trans_decl_ref scope allow_undef expr
  | CallExpr ->
      let callee = C.CallExpr.get_callee expr in
      let args = C.CallExpr.get_args expr in
      trans_call scope skip_lhs fundec_opt loc callee args
  | CStyleCastExpr ->
      let qt = C.CastExpr.get_type expr in
      let operand = C.CastExpr.get_sub_expr expr in
      let typ = trans_type scope qt in
      let is_void = match typ with Cil.TVoid _ -> true | _ -> false in
      let sl, expr_opt =
        (* skip_lhs is true if casting to void i.e. don't mind the variable or return value *)
        trans_expr ~allow_undef ~skip_lhs:is_void scope fundec_opt loc action
          operand
      in
      if is_void then (sl, None)
      else
        let e = Option.get expr_opt in
        (sl, Some (Cil.CastE (typ, e)))
  | ImplicitCastExpr ->
      let qt = C.CastExpr.get_type expr in
      let operand = C.CastExpr.get_sub_expr expr in
      let typ = trans_type scope qt in
      let is_void = match typ with Cil.TVoid _ -> true | _ -> false in
      let sl, expr_opt =
        (* skip_lhs is true if casting to void i.e. don't mind the variable or return value *)
        trans_expr ~allow_undef ~skip_lhs:is_void scope fundec_opt loc action
          operand
      in
      if is_void then (sl, None)
      else
        let e = Option.get expr_opt in
        if should_ignore_implicit_cast ~is_ignore_fun_ptr_decay expr qt e typ
        then (sl, Some e)
        else (sl, Some (Cil.CastE (typ, e)))
  | MemberExpr ->
      let base = C.MemberExpr.get_base expr in
      let is_arrow = C.MemberExpr.is_arrow expr in
      let field = C.MemberExpr.get_member_decl expr in
      ([], Some (trans_member scope fundec_opt loc base is_arrow field))
  | ArraySubscriptExpr -> (
      let base = C.ArraySubscriptExpr.get_base expr in
      let index = C.ArraySubscriptExpr.get_idx expr in
      let sl1, lexp = trans_expr scope fundec_opt loc action base in
      let sl2, rexp = trans_expr scope fundec_opt loc action index in

      (* for array subscription, lexp and rexp must be exist *)
      let lexp = Option.get lexp in
      let rexp = Option.get rexp in

      (* distinguish base and index *)
      let distinguish e1 e2 =
        if e1 |> Cil.typeOf |> Cil.isPointerType then (e1, e2)
        else
          match CilHelper.remove_cast e1 with
          | Cil.Lval exp' when Cil.isArrayType (exp' |> Cil.typeOfLval) ->
              (e1, e2)
          | Cil.BinOp (_, _, _, Cil.TArray (_, _, _)) -> (e1, e2)
          | _ -> (e2, e1)
      in

      let base, idx = distinguish lexp rexp in

      match CilHelper.remove_cast base with
      (* base = arr *)
      | Cil.Lval base' when Cil.isArrayType (base' |> Cil.typeOfLval) ->
          let new_lval =
            Cil.addOffsetLval (Cil.Index (idx, Cil.NoOffset)) base'
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval))
      (* base = (arr+i) *)
      | Cil.BinOp (_, _, _, Cil.TArray (t, _, _)) ->
          let new_lval =
            ( Cil.Mem (Cil.BinOp (Cil.PlusPI, base, idx, Cil.TPtr (t, []))),
              Cil.NoOffset )
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval))
      (* base = (ptr+i) *)
      | _ when Cil.isPointerType (Cil.typeOf base) ->
          let new_lval =
            ( Cil.Mem (Cil.BinOp (Cil.PlusPI, base, idx, Cil.typeOf base)),
              Cil.NoOffset )
          in
          (sl1 @ sl2, Some (Cil.Lval new_lval))
      | _ -> failwith "ArraySubscript")
  | BinaryConditionalOperator -> trans_binary_cond_op scope fundec_opt loc expr
  | ConditionalOperator -> trans_cond_op scope fundec_opt loc expr
  | UnaryExprOrTypeTraitExpr -> trans_unary_expr scope fundec_opt loc expr
  | InitListExpr ->
      (* TODO: https://github.com/prosyslab/sparrow/issues/27 *)
      L.warn "Warning: init list @ %s\n" (CilHelper.s_location loc);
      ([], Some Cil.zero)
  | StmtExpr ->
      (* TODO *)
      L.warn "Warning: stmtexpr @ %s\n" (CilHelper.s_location loc);
      ([], Some Cil.zero)
  | DesignatedInitExpr ->
      trans_expr scope fundec_opt loc action
        (C.DesignatedInitExpr.get_init expr)
  | ImplicitValueInitExpr -> ([], Some Cil.zero)
  | PredefinedExpr ->
      let cstr =
        Cil.CStr
          (C.PredefinedExpr.get_function_name expr |> C.StringLiteral.get_string)
      in
      let const = Cil.Const cstr in
      ([], Some const)
  | ConstantExpr ->
      C.ConstantExpr.get_sub_expr expr
      |> trans_expr ~allow_undef ~skip_lhs ~default_ptr ~is_ignore_fun_ptr_decay
           scope fundec_opt loc action
  | VAArgExpr ->
      (* TODO *)
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
  | ParenExpr ->
      C.ParenExpr.get_sub_expr expr |> trans_expr scope fundec_opt loc action
  | OpaqueValueExpr ->
      C.OpaqueValueExpr.get_source_expr expr
      |> trans_expr scope fundec_opt loc action
  | CompoundLiteralExpr ->
      (* see https://en.cppreference.com/w/c/language/compound_literal *)
      trans_compound_literal_expr scope fundec_opt loc expr
  | _ ->
      L.warn ~to_consol:true "Unknown expr %s at %s\n"
        (C.Expr.get_kind_name expr)
        (CilHelper.s_location loc);
      ([], Some Cil.zero)

and trans_compound_literal_expr scope fundec_opt loc expr =
  let fundec = Option.get fundec_opt in
  let typ = C.CompoundLiteralExpr.get_type expr |> trans_type scope in
  let varinfo, scope = create_local_variable scope fundec "tmp" typ in
  let lv = (Cil.Var varinfo, Cil.NoOffset) in
  let stmts =
    C.CompoundLiteralExpr.get_initializer expr
    |> handle_stmt_init scope typ fundec loc ADrop lv
    |> fst
  in
  (stmts, Some (Cil.Lval lv))

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
  | C.UnaryOperatorKind.PostInc ->
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
  | PostDec ->
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
  | PreInc ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.PlusPI else Cil.PlusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], Some var)
  | PreDec ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.MinusPI else Cil.MinusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], Some var)
  | AddrOf ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      (sl, Some (Cil.AddrOf (lval_of_expr var)))
  | Deref ->
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
  | Plus ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      (sl, Some var)
  | Minus ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.Neg, var, typ)))
  | Not ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.BNot, var, typ)))
  | LNot ->
      let sl, var_opt = trans_expr scope fundec_opt loc action expr in
      let var = get_var var_opt in
      let typ = Cil.typeOf var in
      (sl, Some (Cil.UnOp (Cil.LNot, var, typ)))
  | Extension ->
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
  | C.BinaryOperatorKind.Mul | Div | Rem | Add | Sub | Shl | Shr | LT | GT | LE
  | GE | EQ | NE | And | Xor | Or | LAnd | LOr ->
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
  | Assign -> (
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
  | MulAssign | DivAssign | RemAssign | AddAssign | SubAssign | ShlAssign
  | ShrAssign | AndAssign | XorAssign | OrAssign ->
      let drop_assign = function
        | C.BinaryOperatorKind.MulAssign -> C.BinaryOperatorKind.Mul
        | DivAssign -> Div
        | RemAssign -> Rem
        | AddAssign -> Add
        | SubAssign -> Sub
        | ShlAssign -> Shl
        | ShrAssign -> Shr
        | AndAssign -> And
        | XorAssign -> Xor
        | OrAssign -> Or
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
  | Comma -> (rhs_sl @ lhs_sl, Some rhs_expr)
  | Cmp | PtrMemD | PtrMemI -> failwith "unsupported expr"

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
  let _, bexp = trans_expr scope fundec_opt loc ADrop base in
  match bexp with
  | Some e when arrow ->
      let typ = Cil.typeOf e in
      let fieldinfo =
        match Cil.unrollTypeDeep typ with
        | Cil.TPtr (TComp (comp, _), _) ->
            let name =
              match C.Decl.get_kind field with
              | C.DeclKind.FieldDecl -> C.FieldDecl.get_name field
              | _ -> "unknown"
            in
            List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
        | _ -> failwith "fail"
      in
      if fieldinfo.Cil.fname = "" then e
      else
        Cil.Lval (Cil.mkMem ~addr:e ~off:(Cil.Field (fieldinfo, Cil.NoOffset)))
  | Some (Cil.Lval lv) when not arrow -> (
      let typ = Cil.typeOfLval lv in
      match Cil.unrollTypeDeep typ with
      | Cil.TComp (comp, _) ->
          let name =
            match C.Decl.get_kind field with
            | C.DeclKind.FieldDecl -> C.FieldDecl.get_name field
            | _ -> "unknown"
          in
          let fieldinfo =
            List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
          in
          if fieldinfo.Cil.fname = "" then Cil.Lval lv
          else
            Cil.Lval
              (Cil.addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv)
      | Cil.TPtr (TComp (comp, _), _) ->
          (* this case is counterintuitive but it's required to parse
             the code referencing the anonymous struct inside struct *)
          let name =
            match C.Decl.get_kind field with
            | C.DeclKind.FieldDecl -> C.FieldDecl.get_name field
            | _ -> "unknown"
          in
          let fieldinfo =
            List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
          in
          if fieldinfo.Cil.fname = "" then Option.get bexp
          else
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
      failwith "error bexp = none"

and trans_binary_cond_op scope fundec_opt loc expr =
  let cond = C.BinaryConditionalOperator.get_cond expr in
  let else_branch = C.BinaryConditionalOperator.get_false_expr expr in
  trans_cond_op_internal scope fundec_opt loc cond None else_branch

and trans_cond_op scope fundec_opt loc expr =
  let cond = C.ConditionalOperator.get_cond expr in
  let true_branch = C.ConditionalOperator.get_true_expr expr in
  let else_branch = C.ConditionalOperator.get_false_expr expr in
  trans_cond_op_internal scope fundec_opt loc cond true_branch else_branch

and trans_cond_op_internal scope fundec_opt loc cond then_branch else_branch =
  let scope = Scope.enter_block scope in
  let cond_sl, cond_expr = trans_expr scope fundec_opt loc AExp cond in
  let then_sl, then_expr =
    match then_branch with
    | Some tb ->
        trans_expr ~is_ignore_fun_ptr_decay:false scope fundec_opt loc ADrop tb
    | None -> ([], None)
  in
  let else_sl, else_expr =
    trans_expr ~is_ignore_fun_ptr_decay:false scope fundec_opt loc ADrop
      else_branch
  in
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

and trans_unary_expr scope fundec_opt loc e =
  let kind = C.UnaryExprOrTypeTraitExpr.get_kind e in
  match kind with
  | C.UnaryExprOrTypeTraitExpr.SizeOf
    when C.UnaryExprOrTypeTraitExpr.is_argument_type e ->
      let t = C.UnaryExprOrTypeTraitExpr.get_argument_type e in
      let typ = trans_type scope t in
      ([], Some (Cil.SizeOf typ))
  | SizeOf -> (
      let e = C.UnaryExprOrTypeTraitExpr.get_argument_expr e in
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.SizeOfE e)) | None -> ([], None))
  | (AlignOf | VecStep | OpenMPRequiredSimdAlign | PreferredAlignOf)
    when C.UnaryExprOrTypeTraitExpr.is_expr e -> (
      let e = C.UnaryExprOrTypeTraitExpr.get_argument_expr e in
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.AlignOfE e)) | None -> ([], None))
  | AlignOf | VecStep | OpenMPRequiredSimdAlign | PreferredAlignOf ->
      let t = C.UnaryExprOrTypeTraitExpr.get_argument_type e in
      let typ = trans_type scope t in
      ([], Some (Cil.AlignOf typ))

and trans_stmt scope fundec stmt : Chunk.t * Scope.t =
  let loc = C.Stmt.get_source_location stmt |> trans_location in
  match C.Stmt.get_kind stmt with
  | C.StmtKind.NullStmt | AttributedStmt ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr []) ] }, scope)
  | CompoundStmt ->
      (* CIL does not need to have local blocks because all variables have unique names *)
      C.CompoundStmt.body_list stmt |> trans_compound scope fundec
  | ForStmt ->
      let init = C.ForStmt.get_init stmt in
      let cond_var = C.ForStmt.get_condition_variable stmt in
      let cond = C.ForStmt.get_cond stmt in
      let inc = C.ForStmt.get_inc stmt in
      let body = C.ForStmt.get_body stmt in
      trans_for scope fundec loc init cond_var cond inc body
  | CXXForRangeStmt ->
      failwith ("Unsupported syntax : " ^ CilHelper.s_location loc)
  | IfStmt -> trans_if scope fundec loc stmt
  | SwitchStmt -> trans_switch scope fundec loc stmt
  | CaseStmt -> trans_case scope fundec loc stmt
  | DefaultStmt -> trans_default scope fundec loc stmt
  | WhileStmt -> trans_while scope fundec loc stmt
  | DoStmt -> trans_do scope fundec loc stmt
  | LabelStmt -> trans_label scope fundec loc stmt
  | GotoStmt ->
      let label = C.GotoStmt.get_label stmt |> C.LabelDecl.get_name in
      (trans_goto loc label, scope)
  | ContinueStmt ->
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Continue loc) ] },
        scope )
  | BreakStmt ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Break loc) ] }, scope)
  | GCCAsmStmt | MSAsmStmt ->
      let instr = Cil.Asm ([], [ "asm" ], [], [], [], Cil.locUnknown) in
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr [ instr ]) ] },
        scope )
  | ReturnStmt -> (
      match C.ReturnStmt.get_ret_value stmt with
      | None ->
          let stmts = [ Cil.mkStmt (Cil.Return (None, loc)) ] in
          ({ Chunk.empty with stmts }, scope)
      | Some e -> (
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
              ({ Chunk.empty with stmts }, scope)))
  | DeclStmt ->
      let dl = C.DeclStmt.decl_list stmt in
      let stmts, user_typs, scope =
        trans_var_decl_list scope fundec loc AExp dl
      in
      ({ Chunk.empty with stmts; user_typs }, scope)
  | _ when C.Stmt.is_expr stmt ->
      (* skip_lhs is true here: a function is called at the top-most level
       * without a return variable *)
      let stmts, _ =
        trans_expr ~skip_lhs:true scope (Some fundec) loc ADrop stmt
      in
      ({ Chunk.empty with stmts }, scope)
  | _ ->
      (*       C.Ast.pp_stmt F.err_formatter stmt ; *)
      let stmts = [ Cil.dummyStmt ] in
      ({ Chunk.empty with stmts }, scope)

and trans_compound scope fundec sl =
  let scope = scope |> Scope.enter_block in
  ( List.fold_left
      (fun (l, scope) s ->
        let chunk, scope = trans_stmt scope fundec s in
        (Chunk.append l chunk, scope))
      (Chunk.empty, scope) sl
    |> fst,
    scope |> Scope.exit_block )

and trans_var_decl_list scope fundec loc action dl =
  List.fold_left
    (fun (sl, user_typs, scope) d ->
      match C.Decl.get_kind d with
      | C.DeclKind.VarDecl ->
          let storage = trans_storage d in
          let decl_stmts, scope =
            trans_var_decl ~storage scope fundec loc action d
          in
          (sl @ decl_stmts, user_typs, scope)
      | RecordDecl when C.RecordDecl.is_complete_definition d ->
          let is_struct = C.RecordDecl.is_struct d in
          let new_name, is_new_anon = new_record_id is_struct d in
          let callback compinfo =
            C.RecordDecl.field_list d
            |> List.fold_left
                 (fun fl decl ->
                   match C.Decl.get_kind decl with
                   | C.DeclKind.FieldDecl ->
                       fl @ [ trans_field_decl scope compinfo decl ]
                   | C.DeclKind.IndirectFieldDecl ->
                       fl @ trans_indirect_field_decl scope compinfo decl
                   | _ -> fl)
                 []
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
      | RecordDecl ->
          let is_struct = C.RecordDecl.is_struct d in
          let name, is_new_anon = new_record_id is_struct d in
          let callback compinfo =
            C.RecordDecl.field_list d
            |> List.fold_left
                 (fun fl decl ->
                   match C.Decl.get_kind decl with
                   | C.DeclKind.FieldDecl ->
                       fl @ [ trans_field_decl scope compinfo decl ]
                   | C.DeclKind.IndirectFieldDecl ->
                       fl @ trans_indirect_field_decl scope compinfo decl
                   | _ -> fl)
                 []
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
      | TypedefDecl ->
          let ttype = C.TypedefDecl.get_underlying_type d |> trans_type scope in
          let tname = C.TypedefDecl.get_name d in
          let tinfo = { Cil.tname; ttype; treferenced = false } in
          let scope = Scope.add_type tname (Cil.TNamed (tinfo, [])) scope in
          (sl, user_typs @ [ Cil.GType (tinfo, loc) ], scope)
      | EnumDecl ->
          let globals, scope =
            trans_global_decl ~new_name:(new_enum_id d |> fst) scope d
          in
          (sl, user_typs @ globals, scope)
      | FunctionDecl ->
          (* if the program is valid, there must be the corresponding def somewhere *)
          (sl, user_typs, scope)
      | _ ->
          L.warn ~to_consol:false "Unknown var decl %s\n"
            (CilHelper.s_location loc);
          (sl, [], scope))
    ([], [], scope) dl

and trans_var_decl ?(storage = Cil.NoStorage) (scope : Scope.t) fundec loc
    action desc =
  let typ = C.VarDecl.get_type desc |> trans_type scope in
  let varinfo, scope =
    create_local_variable scope fundec (C.VarDecl.get_name desc) typ
  in
  varinfo.vstorage <- storage;
  match C.VarDecl.get_init desc with
  | Some e ->
      let lv = (Cil.Var varinfo, Cil.NoOffset) in
      handle_stmt_init scope typ fundec loc action lv e
  | _ -> ([], scope)

and handle_stmt_init scope typ fundec loc action lv e =
  let is_primitive_typ typ =
    match Cil.unrollType typ with Cil.TComp (_, _) -> false | _ -> true
  in
  let is_struct_typ typ = not (is_primitive_typ typ) in
  match (C.Expr.get_kind e, Cil.unrollType typ) with
  | C.StmtKind.InitListExpr, Cil.TArray (_, None, _) | InitListExpr, Cil.TPtr _
    ->
      ([], scope)
  (* primitive array *)
  | InitListExpr, Cil.TArray (arr_typ, Some arr_exp, _)
    when is_primitive_typ arr_typ ->
      C.InitListExpr.get_inits e
      |> mk_arr_stmt scope fundec loc action lv arr_exp
  (* struct array *)
  | InitListExpr, Cil.TArray (arr_typ, Some arr_exp, _)
    when is_struct_typ arr_typ ->
      let el = C.InitListExpr.get_inits e in
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
  | InitListExpr, Cil.TComp (ci, _) ->
      let el = C.InitListExpr.get_inits e in
      let stmts, _, scope =
        mk_local_struct_init scope ci.cfields fundec action loc lv el
      in
      (stmts, scope)
  (* primitive init list (contains only one element) *)
  | InitListExpr, _ ->
      let el = C.InitListExpr.get_inits e in
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
  let scope = scope |> Scope.enter_block in
  let arr_len =
    match len_exp with
    | Cil.Const (CInt64 (v, _, _)) -> Int64.to_int v
    | _ -> failwith "not expected"
  in
  let arr_init idx_list =
    match idx_list with
    | [] -> []
    | _ ->
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
    let tmp_var_lval, tmp_var_expr, tmp_var_stmt, unary_plus_expr, scope =
      mk_tmp_var fundec loc (List.length el) scope
    in

    (* arr[tmp] = 0 *)
    let lv = Cil.addOffsetLval (Cil.Index (tmp_var_expr, Cil.NoOffset)) lv in
    let var_instr = Cil.Instr [ Cil.Set (lv, Cil.integer 0, loc) ] in
    let var_stmt = Cil.mkStmt var_instr in

    (* while *)
    let while_stmt =
      mk_while_stmt arr_len loc tmp_var_expr tmp_var_lval unary_plus_expr
        [ var_stmt ]
    in
    (sl @ [ tmp_var_stmt ] @ while_stmt, scope |> Scope.exit_block)
  else (arr_init idx_list, scope |> Scope.exit_block)

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

and trans_var_decl_opt scope fundec loc vdecl =
  match vdecl with
  | Some v -> trans_var_decl scope fundec loc AExp v
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
    scope |> Scope.exit_block )

and trans_while scope fundec loc stmt =
  let condition_variable = C.WhileStmt.get_condition_variable stmt in
  let cond = C.WhileStmt.get_cond stmt in
  let body = C.WhileStmt.get_body stmt in
  let decl_stmt, scope =
    trans_var_decl_opt scope fundec loc condition_variable
  in
  let cond_stmt, cond_expr_opt = trans_expr scope (Some fundec) loc AExp cond in
  let cond_expr = get_opt "while_cond" cond_expr_opt in
  let break_stmt = Cil.mkBlock [ Cil.mkStmt (Cil.Break loc) ] in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    match Cil.constFold false cond_expr |> Cil.isInteger with
    | Some i64 when Cil.i64_to_int i64 = 1 -> body_stmt.Chunk.stmts
    | _ ->
        cond_stmt
        @ Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc))
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

and trans_do scope fundec loc stmt =
  let cond = C.DoStmt.get_cond stmt in
  let body = C.DoStmt.get_body stmt in
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

and trans_if scope fundec loc stmt =
  let init = C.IfStmt.get_init stmt in
  let cond_var = C.IfStmt.get_condition_variable stmt in
  let cond = C.IfStmt.get_cond stmt in
  let then_branch = C.IfStmt.get_then stmt in
  let else_branch = C.IfStmt.get_else stmt in
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
  match C.Stmt.get_kind body with
  | C.StmtKind.CompoundStmt ->
      C.CompoundStmt.body_list body |> trans_compound scope fundec |> fst
  | _ -> trans_stmt scope fundec body |> fst

and trans_switch scope fundec loc stmt =
  let init, _ = C.SwitchStmt.get_init stmt |> trans_stmt_opt scope fundec in
  let decl_sl, scope =
    C.SwitchStmt.get_condition_variable stmt
    |> trans_var_decl_opt scope fundec loc
  in
  let cond_sl, cond_expr_opt =
    C.SwitchStmt.get_cond stmt |> trans_expr scope (Some fundec) loc AExp
  in
  let cond_expr = Option.get cond_expr_opt in
  let body_stmt =
    C.SwitchStmt.get_body stmt |> trans_stmt scope fundec |> fst
  in
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

and trans_case scope fundec loc stmt =
  let lhs_expr =
    C.CaseStmt.get_lhs stmt |> trans_expr scope (Some fundec) loc ADrop |> snd
  in
  let chunk = C.CaseStmt.get_sub_stmt stmt |> trans_stmt scope fundec |> fst in
  let label = Cil.Case (Option.get lhs_expr, loc) in
  match chunk.Chunk.stmts with
  | h :: _ ->
      h.labels <- h.labels @ [ label ];
      ({ chunk with cases = h :: chunk.cases }, scope)
  | [] -> (chunk, scope)

and trans_default scope fundec loc stmt =
  let chunk =
    C.DefaultStmt.get_sub_stmt stmt |> trans_stmt scope fundec |> fst
  in
  let label = Cil.Default loc in
  match chunk.Chunk.stmts with
  | h :: _ ->
      h.labels <- label :: h.labels;
      ({ chunk with cases = chunk.cases @ [ h ] }, scope)
  | [] -> (chunk, scope)

and trans_label scope fundec loc stmt =
  let label = C.LabelStmt.get_name stmt in
  let body = C.LabelStmt.get_sub_stmt stmt in
  (* Clang frontend guarantees the uniqueness of label names,
   * so do not need to create unique names.
   * Instead, we only add the label name to the scope,
   * to avoid conflicts with CIL-generated label names.
   * Note that scope is not updated here, as it should have
   * been handled in advance (trans_function_body)
   *)
  let chunk = trans_stmt scope fundec body |> fst in
  (append_label chunk label loc true, scope)

and trans_stmt_opt scope fundec = function
  | Some s -> trans_stmt scope fundec s
  | None -> (Chunk.empty, scope)

and trans_global_decl ?(new_name = "") scope (decl : C.Decl.t) =
  let loc = C.Decl.get_source_location decl |> trans_location in
  let storage = trans_storage decl in
  match C.Decl.get_kind decl with
  | C.DeclKind.FunctionDecl when C.Decl.is_implicit decl -> ([], scope)
  | FunctionDecl when C.FunctionDecl.does_this_declaration_have_a_body decl ->
      let name = C.FunctionDecl.get_name decl in
      let fundec = Cil.emptyFunction name in
      let typ = Cil.TFun (Cil.voidType, None, false, []) in
      let svar, scope = find_global_variable scope name typ in
      let scope = Scope.enter_function scope in
      let function_type = C.FunctionDecl.get_type decl in
      let typ, scope =
        trans_function_type scope (Some fundec) (Some decl) function_type
      in
      fundec.svar <- svar;
      fundec.svar.vtype <- typ;
      fundec.svar.vstorage <- storage;
      fundec.svar.vattr <- trans_decl_attribute (C.FunctionDecl.get_attrs decl);
      fundec.svar.vinline <- C.FunctionDecl.is_inline_specified decl;
      let fun_body =
        C.FunctionDecl.get_body decl
        |> Option.get
        |> trans_function_body scope fundec
      in
      fundec.sbody <- fst fun_body;
      let scope = Scope.exit_function scope in
      CilHelper.insert_missing_return fundec;
      (snd fun_body @ [ Cil.GFun (fundec, loc) ], scope)
  | FunctionDecl ->
      let name = C.FunctionDecl.get_name decl in
      let typ = Cil.TFun (Cil.voidType, None, false, []) in
      let svar, scope = find_global_variable scope name typ in
      let scope = Scope.enter_function scope in
      let function_type = C.FunctionDecl.get_type decl in
      let typ, scope =
        trans_function_type scope None (Some decl) function_type
      in
      svar.vtype <- typ;
      svar.vstorage <- storage;
      svar.vattr <- trans_decl_attribute (C.FunctionDecl.get_attrs decl);
      let scope = Scope.exit_function scope in
      ([ Cil.GVarDecl (svar, loc) ], scope)
  | VarDecl when C.VarDecl.has_init decl ->
      let typ = C.VarDecl.get_type decl |> trans_type scope in
      let name = C.VarDecl.get_name decl in
      let vi, scope = find_global_variable scope name typ in
      vi.vstorage <- storage;
      let e = C.VarDecl.get_init decl |> Option.get in
      let init = Some (trans_global_init scope loc typ e) in
      vi.vinit.init <- init;
      ([ Cil.GVar (vi, { Cil.init }, loc) ], scope)
  | VarDecl ->
      let typ = C.VarDecl.get_type decl |> trans_type scope in
      let name = C.VarDecl.get_name decl in
      let vi, scope = find_global_variable scope name typ in
      vi.vstorage <- storage;
      ([ Cil.GVarDecl (vi, loc) ], scope)
  | RecordDecl when C.RecordDecl.is_complete_definition decl ->
      let is_struct = C.RecordDecl.is_struct decl in
      let globals, scope =
        C.RecordDecl.field_list decl
        |> List.fold_left
             (fun (globals, scope) decl ->
               let gs, scope = trans_global_decl scope decl in
               (globals @ gs, scope))
             ([], scope)
      in
      let callback compinfo =
        List.fold_left
          (fun fl decl ->
            match C.Decl.get_kind decl with
            | C.DeclKind.FieldDecl ->
                fl @ [ trans_field_decl scope compinfo decl ]
            | C.DeclKind.IndirectFieldDecl ->
                fl @ trans_indirect_field_decl scope compinfo decl
            | _ -> fl)
          []
          (C.RecordDecl.field_list decl)
      in
      let name =
        if new_name = "" then new_record_id is_struct decl |> fst else new_name
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
  | RecordDecl ->
      let is_struct = C.RecordDecl.is_struct decl in
      let name =
        if new_name = "" then new_record_id is_struct decl |> fst else new_name
      in
      if Scope.mem_comp name scope then
        let typ = Scope.find_comp name scope in
        let prev_ci = get_compinfo typ in
        ([ Cil.GCompTagDecl (prev_ci, loc) ], scope)
      else
        let callback _ = [] in
        let compinfo = Cil.mkCompInfo is_struct name callback [] in
        let typ = Cil.TComp (compinfo, []) in
        let scope = Scope.add_comp name typ scope in
        ([ Cil.GCompTagDecl (compinfo, loc) ], scope)
  | TypedefDecl when C.TypedefDecl.is_implicit decl -> ([], scope)
  | TypedefDecl ->
      let ttype = C.TypedefDecl.get_underlying_type decl |> trans_type scope in
      let name = C.TypedefDecl.get_name decl in
      let tinfo = { Cil.tname = name; ttype; treferenced = false } in
      let scope = Scope.add_type name (Cil.TNamed (tinfo, [])) scope in
      ([ Cil.GType (tinfo, loc) ], scope)
  | EnumDecl ->
      let eitems, scope, _ =
        C.EnumDecl.get_enums decl
        |> List.fold_left
             (fun (eitems, scope, next) c ->
               let value =
                 C.EnumConstantDecl.get_init_val c
                 |> Int64.to_int |> Cil.integer
               in
               let name = C.EnumConstantDecl.get_name c in
               let scope = Scope.add name (EnvData.EnvEnum value) scope in
               (eitems @ [ (name, value, loc) ], scope, next))
             ([], scope, Cil.zero)
      in
      let name =
        if new_name = "" then
          let name = C.EnumDecl.get_name decl in
          if name = "" then new_enum_id decl |> fst else name
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
      let scope = Scope.add_type name (Cil.TEnum (einfo, [])) scope in
      ([ Cil.GEnumTag (einfo, loc) ], scope)
  | FieldDecl | IndirectFieldDecl | EmptyDecl | AccessSpecDecl | NamespaceDecl
  | UsingDirectiveDecl | CXXConstructorDecl | CXXDestructorDecl
  | LinkageSpecDecl | FriendDecl | NamespaceAliasDecl | StaticAssertDecl
  | TypeAliasDecl | DecompositionDecl ->
      ([], scope)
  | _ ->
      failwith
        ("Unknown decl " ^ C.Decl.get_kind_name decl ^ " at "
       ^ CilHelper.s_location loc)

and trans_function_body scope fundec body =
  let scope =
    match C.Stmt.get_kind body with
    | C.StmtKind.CompoundStmt ->
        C.CompoundStmt.body_list body |> add_labels scope
    | _ -> scope
  in
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
                    match C.Stmt.get_kind e with
                    | C.StmtKind.DesignatedInitExpr ->
                        C.DesignatedInitExpr.get_init e :: el
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

and trans_global_init scope loc typ e =
  match (C.Expr.get_kind e, Cil.unrollType typ) with
  | C.StmtKind.InitListExpr, Cil.TArray (elt_typ, None, _) ->
      let el = C.InitListExpr.get_inits e in
      let init_list =
        List.fold_left
          (fun (r, o) i ->
            let init = trans_global_init scope loc elt_typ i in
            ((Cil.Index (Cil.integer o, Cil.NoOffset), init) :: r, o + 1))
          ([], 0) el
        |> fst |> List.rev
      in
      Cil.CompoundInit (typ, init_list)
  | InitListExpr, Cil.TArray (elt_typ, Some len_exp, _) ->
      let el = C.InitListExpr.get_inits e in
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
  | InitListExpr, Cil.TComp (ci, _) ->
      let el = C.InitListExpr.get_inits e in
      mk_global_struct_init scope loc typ ci.cfields el |> fst
  | InitListExpr, _ ->
      let el = C.InitListExpr.get_inits e in
      if el <> [] then
        (* accept only first scalar and ignore remainder *)
        List.hd el |> trans_expr scope None loc ADrop |> snd |> Option.get
        |> fun x -> Cil.SingleInit x
      else
        trans_expr scope None loc ADrop e |> snd |> Option.get |> fun x ->
        Cil.SingleInit x
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

let split_decl tu =
  C.TranslationUnit.fold_left_decls
    (fun (types, vars) decl ->
      match C.Decl.get_kind decl with
      | C.DeclKind.FunctionDecl | C.DeclKind.VarDecl -> (types, decl :: vars)
      | _ -> (decl :: types, vars))
    ([], []) tu
  |> fun (ts, vs) -> (List.rev ts, List.rev vs)

let parse fname =
  let tu = C.TranslationUnit.parse_file [| fname |] in
  let scope = initialize_builtins (Scope.create ()) in
  (* to make it consistent with CIL, translate types first, vars next *)
  let types, vars = split_decl tu in
  let globals =
    List.fold_left
      (fun (globals, scope) decl ->
        let new_globals, scope = trans_global_decl scope decl in
        (List.rev_append new_globals globals, scope))
      ([], scope) (types @ vars)
    |> fst |> List.rev
  in
  {
    Cil.fileName = fname;
    Cil.globals;
    Cil.globinit = None;
    Cil.globinitcalled = false;
  }
