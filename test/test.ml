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
let analyzer = "../bin/sparrow"

let default_opt = "-verbose 0"

type test_suite = { opt : string; files : string list }

let test_suites =
  [
    {
      opt = "";
      files =
        [
          "basic/array_pointer.c";
          "basic/global_array.c";
          "basic/global_static_struct.c";
          "basic/global_static_struct2.c";
          "basic/local_dynamic_struct.c";
          "basic/local_static_struct.c";
          "basic/struct_pointer.c";
          "interval/prune_const.c";
          "interval/strncpy.c";
          "interval/memcpy.c";
          "interval/memset.c";
        ];
    };
    { opt = "-narrow"; files = [ "narrowing/narrow.c" ] };
    {
      opt = "-inline alloc -unsound_alloc";
      files = [ "unsoundness/unsound_alloc.c" ];
    };
    {
      opt = "-taint";
      files =
        [
          "taint/printf.c";
          "taint/varg.c";
          "taint/snprintf.c";
          "taint/strtok.c";
          "taint/fgetc.c";
          "taint/asprintf.c";
          "taint/memcpy.c";
        ];
    };
    {
      opt = "-frontend clang -il";
      files =
        [
          "clang/global-array0.c";
          "clang/local-array0.c";
          "clang/struct0.c";
          "clang/struct1.c";
          "clang/struct2.c";
          "clang/struct3.c";
          "clang/struct4.c";
          "clang/struct5.c";
          "clang/struct6.c";
          "clang/struct7.c";
          "clang/implicit-cast0.c";
          "clang/implicit-cast1.c";
          "clang/implicit-cast2.c";
          "clang/implicit-cast3.c";
          "clang/implicit-cast4.c";
          "clang/binop0.c";
          "clang/ternop0.c";
          "clang/ternop1.c";
          "clang/ternop2.c";
          "clang/ternop3.c";
          "clang/enum0.c";
          "clang/enum1.c";
          "clang/enum2.c";
          "clang/pointer0.c";
          "clang/pointer1.c";
          "clang/pointer2.c";
          "clang/pointer3.c";
          "clang/pointer4.c";
          "clang/pointer5.c";
          "clang/pointer6.c";
          "clang/namespace0.c";
          "clang/missing-proto0.c";
          "clang/stmtexpr0.c";
          "clang/duplication0.c";
          "clang/switch0.c";
          "clang/switch1.c";
          "clang/while0.c";
          "clang/while1.c";
          "clang/while2.c";
          "clang/goto0.c";
          "clang/goto1.c";
          "clang/goto2.c";
          "clang/goto3.c";
          "clang/attribute0.c";
          "clang/attribute1.c";
          "clang/return0.c";
          "clang/return1.c";
          "clang/return2.c";
          "clang/block0.c";
          "clang/block1.c";
          "clang/function0.c";
          "clang/if0.c";
          "clang/if1.c";
          "clang/if2.c";
          "clang/if3.c";
          "clang/init-list0.c";
          "clang/init-list1.c";
          "clang/init-list2.c";
          "clang/nested-init-0.c";
          "clang/nested-init-1.c";
          "clang/nested-init-2.c";
          "clang/local-init1.c";
          "clang/local-init2.c";
          "clang/local-init3.c";
          "clang/local-init4.c";
          "clang/local-init5.c";
          "clang/local-init6.c";
          "clang/local-init7.c";
          "clang/local-init8.c";
          "clang/local-init9.c";
          "clang/local-init10.c";
          "clang/label0.c";
          "clang/label1.c";
          "clang/label2.c";
          "clang/comma0.c";
          "clang/comma1.c";
          "clang/usertype-in-local0.c";
          "clang/usertype-in-local1.c";
          "clang/usertype-in-local2.c";
          "clang/usertype-in-local3.c";
          "clang/long0.c";
          "clang/long1.c";
          "clang/unicode0.c";
          "clang/static0.c";
          "clang/variable-array0.c";
          "clang/variable-array1.c";
          "clang/duplicated-label0.c";
          "clang/array-subscript0.c";
          "clang/array-subscript1.c";
          "clang/array-subscript2.c";
          "clang/array-subscript3.c";
          "clang/array-subscript4.c";
          "clang/array-init0.c";
          "clang/incomplete-array0.c";
          "clang/designated-init0.c";
          "clang/designated-init1.c";
          "clang/UL0.c";
          "clang/local-fun0.c";
          "clang/unary_operator0.c";
          "clang/anonymous-struct0.c";
          "clang/anonymous-struct1.c";
          "clang/anonymous-struct2.c";
          "clang/indirect-field0.c";
          "clang/indirect-field1.c";
          "clang/indirect-field2.c";
          "clang/indirect-field3.c";
          "clang/type0.c";
          "clang/type1.c";
          "clang/type2.c";
          "clang/param0.c";
          "clang/predef-macro.c";
          "clang/cast0.c";
          "clang/cast1.c";
          "clang/unexposed.c";
          "clang/alignof0.c";
          "clang/alignof1.c";
          "clang/attr-stmt0.c";
          "clang/__int128_t0.c";
          "clang/__uint128_t0.c";
          "clang/vaarg0.c";
        ];
    };
    {
      opt = "-frontend claml -il";
      files =
        [
          "claml/global-array0.c";
          "claml/local-array0.c";
          "claml/struct0.c";
          "claml/struct1.c";
          "claml/struct2.c";
          "claml/struct3.c";
          "claml/struct4.c";
          "claml/struct5.c";
          "claml/struct6.c";
          "claml/struct7.c";
          "claml/implicit-cast0.c";
          "claml/implicit-cast1.c";
          "claml/implicit-cast2.c";
          "claml/implicit-cast3.c";
          "claml/implicit-cast4.c";
          "claml/binop0.c";
          "claml/ternop0.c";
          "claml/ternop1.c";
          "claml/ternop2.c";
          "claml/ternop3.c";
          "claml/enum0.c";
          "claml/enum1.c";
          "claml/enum2.c";
          "claml/pointer0.c";
          "claml/pointer1.c";
          "claml/pointer2.c";
          "claml/pointer3.c";
          "claml/pointer4.c";
          "claml/pointer5.c";
          "claml/pointer6.c";
          "claml/namespace0.c";
          "claml/missing-proto0.c";
          "claml/stmtexpr0.c";
          "claml/duplication0.c";
          "claml/switch0.c";
          "claml/switch1.c";
          "claml/while0.c";
          "claml/while1.c";
          "claml/while2.c";
          "claml/goto0.c";
          "claml/goto1.c";
          "claml/goto2.c";
          "claml/goto3.c";
          "claml/attribute0.c";
          "claml/attribute1.c";
          "claml/return0.c";
          "claml/return1.c";
          "claml/return2.c";
          "claml/block0.c";
          "claml/block1.c";
          "claml/function0.c";
          "claml/if0.c";
          "claml/if1.c";
          "claml/if2.c";
          "claml/if3.c";
          "claml/init-list0.c";
          "claml/init-list1.c";
          "claml/init-list2.c";
          "claml/nested-init-0.c";
          "claml/nested-init-1.c";
          "claml/nested-init-2.c";
          "claml/local-init1.c";
          "claml/local-init2.c";
          "claml/local-init3.c";
          "claml/local-init4.c";
          "claml/local-init5.c";
          "claml/local-init6.c";
          "claml/local-init7.c";
          "claml/local-init8.c";
          "claml/local-init9.c";
          "claml/local-init10.c";
          "claml/label0.c";
          "claml/label1.c";
          "claml/label2.c";
          "claml/comma0.c";
          "claml/comma1.c";
          "claml/usertype-in-local0.c";
          "claml/usertype-in-local1.c";
          "claml/usertype-in-local2.c";
          "claml/usertype-in-local3.c";
          "claml/long0.c";
          "claml/long1.c";
          "claml/unicode0.c";
          "claml/static0.c";
          "claml/variable-array0.c";
          "claml/variable-array1.c";
          "claml/duplicated-label0.c";
          "claml/array-subscript0.c";
          "claml/array-subscript1.c";
          "claml/array-subscript2.c";
          "claml/array-subscript3.c";
          "claml/array-subscript4.c";
          "claml/array-init0.c";
          "claml/incomplete-array0.c";
          "claml/designated-init0.c";
          "claml/designated-init1.c";
          "claml/UL0.c";
          "claml/local-fun0.c";
          "claml/unary_operator0.c";
          "claml/anonymous-struct0.c";
          "claml/anonymous-struct1.c";
          "claml/anonymous-struct2.c";
          "claml/indirect-field0.c";
          "claml/indirect-field1.c";
          "claml/indirect-field2.c";
          "claml/indirect-field3.c";
          "claml/type0.c";
          "claml/type1.c";
          "claml/type2.c";
          "claml/param0.c";
          "claml/predef-macro.c";
          "claml/cast0.c";
          "claml/cast1.c";
          "claml/unexposed.c";
          "claml/alignof0.c";
          "claml/alignof1.c";
          "claml/attr-stmt0.c";
          "claml/__int128_t0.c";
          "claml/__uint128_t0.c";
          "claml/vaarg0.c";
        ];
    };
  ]

let make_cmd opt f =
  analyzer ^ " " ^ default_opt ^ " " ^ opt ^ " " ^ f
  |> Str.split (Str.regexp "[ ]+")
  |> Array.of_list

let run opt f =
  let cmd = make_cmd opt f in
  (try Unix.unlink (f ^ ".out") with _ -> ());
  let fd = Unix.openfile (f ^ ".out") [ Unix.O_CREAT; Unix.O_RDWR ] 0o640 in
  let pid = Unix.create_process analyzer cmd Unix.stdin fd fd in
  ignore (Unix.waitpid [] pid);
  Unix.close fd

let color_green = "\x1B[32m"

let color_red = "\x1B[31m"

let color_reset = "\x1B[0m"

let msg_pass = color_green ^ "PASS" ^ color_reset

let msg_fail = color_red ^ "FAIL" ^ color_reset

let check f =
  let oc = Unix.open_process_out ("diff " ^ f ^ ".answer " ^ f ^ ".out") in
  print_string (f ^ ".....");
  match Unix.close_process_out oc with
  | Unix.WEXITED i when i = 0 ->
      print_endline msg_pass;
      Unix.unlink (f ^ ".out");
      true
  | _ ->
      print_endline (msg_fail ^ " (see " ^ f ^ ".answer and " ^ f ^ ".out)");
      false

let print_result = function
  | true -> print_endline (color_green ^ "All tests are passed" ^ color_reset)
  | false ->
      print_endline (color_red ^ "Test failed" ^ color_reset);
      exit 1

let _ =
  List.fold_left
    (fun c test_suite ->
      List.fold_left
        (fun c f ->
          run test_suite.opt f;
          check f && c)
        c test_suite.files)
    true test_suites
  |> print_result
