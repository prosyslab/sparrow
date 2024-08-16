module Cil = ProsysCil.Cil
open Cil
module SS = Set.Make (String)

type wrapper_type =
  | AllocWrapper of Cil.exp
  | CallocWrapper of (Cil.exp * Cil.exp)
  | NoWrapper

let vptr_return_funcs = ref SS.empty

let vptr_return_fields = ref SS.empty

let unwrapped_funcs = ref SS.empty

let unwrapped_fields = ref SS.empty

let identify_vptr_return_funcs file =
  let check_type is_func name typ =
    match typ with
    | TFun (retTyp, _, _, _) when Cil.isVoidPtrType retTyp ->
        if is_func then vptr_return_funcs := SS.add name !vptr_return_funcs
        else vptr_return_fields := SS.add name !vptr_return_fields
    | _ -> ()
  in
  let check_global = function
    | GFun (fd, _) -> check_type true fd.svar.vname fd.svar.vtype
    | GCompTag (comp, _) ->
        List.iter (fun f -> check_type false f.fname f.ftype) comp.cfields
    | _ -> ()
  in
  List.iter check_global file.Cil.globals

let print_vptr_returns () =
  SS.elements !vptr_return_funcs
  |> Vocab.string_of_list Vocab.id
  |> Logging.info "'void*' returning functions: %s\n";
  SS.elements !vptr_return_fields
  |> Vocab.string_of_list Vocab.id
  |> Logging.info "'void*' returning fields: %s\n"

let add_unwrapped is_func f =
  if is_func then unwrapped_funcs := SS.add f !unwrapped_funcs
  else unwrapped_fields := SS.add f !unwrapped_fields

let print_unwrapped () =
  SS.elements !unwrapped_funcs
  |> Vocab.string_of_list Vocab.id
  |> Logging.info "Unwrapped functions: %s\n";
  SS.elements !unwrapped_fields
  |> Vocab.string_of_list Vocab.id
  |> Logging.info "Unwrapped fields: %s\n"

let malloc =
  Cil.makeGlobalVar "malloc"
    (Cil.TFun (Cil.voidPtrType, Some [ ("", Cil.intType, []) ], false, []))

(* Subsume 'realloc' here. Note that there's no gurantee that 'm' appears. *)
let alloc_re = Str.regexp ".*alloc.*"

let calloc_re = Str.regexp ".*calloc.*"

let is_unrolled_int typ =
  match Cil.unrollType typ with TInt _ -> true | _ -> false

(* Heuristically choose the first integer type argument (for malloc/reallc) *)
let rec extract_alloc_arg is_func name args =
  match args with
  | [] -> NoWrapper
  | head_arg :: tail_args -> (
      match Cil.typeOf head_arg with
      | TInt _ ->
          add_unwrapped is_func name;
          AllocWrapper head_arg
      | _ -> extract_alloc_arg is_func name tail_args)

(* Heuristically choose the first two adjacent integer type arguments *)
let rec extract_calloc_arg is_func name args =
  match args with
  | [] | [ _ ] -> NoWrapper
  | arg1 :: arg2 :: tail_args -> (
      match (Cil.typeOf arg1, Cil.typeOf arg2) with
      | TInt _, TInt _ ->
          add_unwrapped is_func name;
          CallocWrapper (arg1, arg2)
      | TInt _, TNamed _ when is_unrolled_int (Cil.typeOf arg2) ->
          add_unwrapped is_func name;
          CallocWrapper (arg1, arg2)
      | TNamed _, TInt _ when is_unrolled_int (Cil.typeOf arg1) ->
          add_unwrapped is_func name;
          CallocWrapper (arg1, arg2)
      | TNamed _, TNamed _
        when is_unrolled_int (Cil.typeOf arg1)
             && is_unrolled_int (Cil.typeOf arg2) ->
          add_unwrapped is_func name;
          CallocWrapper (arg1, arg2)
      | _ -> extract_calloc_arg is_func name (arg2 :: tail_args))

(* Note that API functions (e.g., "malloc", "realloc") will be also unwrapped by
 * this transformation, which will be harmless. *)
let decide_wrapper is_func name args =
  let is_vptr =
    (is_func && SS.mem name !vptr_return_funcs)
    || SS.mem name !vptr_return_fields
  in
  let s = String.lowercase_ascii name in
  (* Note that 'calloc' check should come first here. *)
  if is_vptr && Str.string_match calloc_re s 0 then
    extract_calloc_arg is_func name args
  else if is_vptr && Str.string_match alloc_re s 0 then
    extract_alloc_arg is_func name args
  else NoWrapper

let trans lvo is_func name args loc =
  match decide_wrapper is_func name args with
  | NoWrapper -> DoChildren
  | AllocWrapper arg ->
      ChangeTo [ Call (lvo, Lval (Var malloc, NoOffset), [ arg ], loc) ]
  | CallocWrapper (arg1, arg2) ->
      let arg = BinOp (Mult, arg1, arg2, Cil.intType) in
      ChangeTo [ Call (lvo, Lval (Var malloc, NoOffset), [ arg ], loc) ]

let rec check_last_offset = function
  | NoOffset -> ""
  | Field (f, NoOffset) -> f.fname
  | Field (_, off) | Index (_, off) -> check_last_offset off

let rec extract_last_field_name = function
  | Lval (_, offsets) -> check_last_offset offsets
  | CastE (_, e) -> extract_last_field_name e
  | _ -> ""

class wrapperVisitor () =
  object
    inherit nopCilVisitor

    method! vinst inst =
      match inst with
      (* Normal call with function names *)
      | Call (lvo, Lval (Var f, NoOffset), args, loc) ->
          trans lvo true f.vname args loc
      (* Indirect call with function pointers *)
      | Call (lvo, Lval (Mem e, NoOffset), args, loc) ->
          trans lvo false (extract_last_field_name e) args loc
      | _ -> DoChildren
  end

let transform file =
  identify_vptr_return_funcs file;
  print_vptr_returns ();
  let vis = new wrapperVisitor () in
  ignore (Cil.visitCilFile vis file);
  print_unwrapped ();
  file
