(* Represent the argument of API functions *)
type arg_typ =
  (* boolean is to mark if this argument should generate buffer access query *)
  (* Source of propagation *)
  | Src of (var * src_typ)
  (* Array where Src arg (& top itv) must be moved to *)
  | Dst of (var * bool)
  (* Array where user input must be stored in *)
  | Buf of (var * bool)
  | StructPtr
  | Size
  | Skip

and var = (* variability of argument *)
  | Fixed | Variable

and src_typ =
  (* The value of source argument must be propagated *)
  | Value
  | Array

type ret_typ =
  | Const
  (* User input value (top itv & taintness) *)
  | TaintInput
  (* Src argument returned *)
  | SrcArg
  (* Integer between 0 ~ Size arg returned *)
  | SizeArg
  (* Top itv & taintness of Src argument returned *)
  | TopWithSrcTaint
  (* Dst argument returned *)
  | DstArg
  (* Buf argument returned *)
  | BufArg
  (* New block, filled with given abstract val. *)
  | AllocConst
  (* New block, filled with user input *)
  | AllocBuf
  (* New block, filled with Src argument *)
  | AllocDst
  (* Newly allocated struct *)
  | AllocStruct

type api_typ = { arg_typs : arg_typ list; ret_typ : ret_typ }

(* Arguments *)

(* arguments that generates query *)
let v_src = Src (Fixed, Value)

let v_src_va = Src (Variable, Value)

let arr_src = Src (Fixed, Array)

let arr_src_va = Src (Variable, Array)

let dst = Dst (Fixed, false)

let dst_alloc = Dst (Fixed, true)

let dst_va = Dst (Variable, false)

let buf = Buf (Fixed, false)

let buf_va = Buf (Variable, false)

(* Fixed return values *)
let ones = Const

let int_v = Const

let tainted_v = TaintInput

let int_arr = AllocConst

let tainted_arr = AllocBuf

module ApiMap = Map.Make (struct
  type t = string

  let compare = Stdlib.compare
end)

let api_map =
  (* <cstring> ( <string.h> ) *)
  ApiMap.empty
  (* Copy *)
  |> ApiMap.add "memcpy" { arg_typs = [ dst; arr_src; Size ]; ret_typ = DstArg }
  |> ApiMap.add "memmove"
       { arg_typs = [ dst; arr_src; Size ]; ret_typ = DstArg }
  |> ApiMap.add "strcpy" { arg_typs = [ dst; arr_src ]; ret_typ = DstArg }
  |> ApiMap.add "g_strdup" { arg_typs = [ arr_src ]; ret_typ = AllocDst }
  |> ApiMap.add "strncpy"
       { arg_typs = [ dst; arr_src; Size ]; ret_typ = DstArg }
  |> ApiMap.add "strxfrm"
       { arg_typs = [ dst; arr_src; Size ]; ret_typ = TopWithSrcTaint }
  (* Concatenation *)
  |> ApiMap.add "strcat" { arg_typs = [ dst; arr_src ]; ret_typ = DstArg }
  (* XXX *)
  |> ApiMap.add "strncat"
       { arg_typs = [ dst; arr_src; Size ]; ret_typ = DstArg }
  (* Comparison *)
  (* XXX *)
  |> ApiMap.add "memcmp"
       { arg_typs = [ arr_src; arr_src; Size ]; ret_typ = ones }
  |> ApiMap.add "strcmp" { arg_typs = [ arr_src; arr_src ]; ret_typ = ones }
  |> ApiMap.add "strcoll" { arg_typs = [ arr_src; arr_src ]; ret_typ = ones }
  |> ApiMap.add "strncmp"
       { arg_typs = [ arr_src; arr_src; Size ]; ret_typ = ones }
  (* Searching *)
  |> ApiMap.add "memchr"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "memrchr"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "rawmemchr" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strchr" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strcspn"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = int_v }
  (* Unlike strchr, this returns the offset of occuring substring *)
  |> ApiMap.add "strpbrk" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strrchr" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strspn" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strstr" { arg_typs = [ arr_src; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strtok" { arg_typs = [ v_src; Skip; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "strtok_r"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = SrcArg }
  |> ApiMap.add "wcrtomb"
       { arg_typs = [ dst; arr_src; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "mbrtowc"
       { arg_typs = [ dst; arr_src; Skip ]; ret_typ = TopWithSrcTaint }
  (* Others *)
  (* FIXME: Do not assign v_src to the 1st arg. Do assign it to *dst
     * |> ApiMap.add "memset" {arg_typs = [dst; v_src; Size]; ret_typ = DstArg} *)
  |> ApiMap.add "strerror" { arg_typs = [ Skip ]; ret_typ = int_arr }
  |> ApiMap.add "strlen" { arg_typs = [ arr_src ]; ret_typ = int_v }
  (* Character conversion (<ctype.h>) *)
  |> ApiMap.add "tolower" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "towlower" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "toupper" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  (* Mathmatical (<math.h>) *)
  |> ApiMap.add "log" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "sin" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "tan" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "cos" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "acos" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "asin" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "atan" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "atan2" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "pow" { arg_typs = [ v_src; v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "sqrt" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "abs" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "fabs" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "ceil" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "floor" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "exp" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "expf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "expl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "cosh" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "coshf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "coshl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "sinh" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "sinhf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "sinhl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "log10" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "log10f" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "log10l" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "lgamma" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "lgammaf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "lgammal" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erff" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erfl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erfc" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erfcf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "erfcl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "round" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "roundl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "roundf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "lroundl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "lroundf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "llround" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "fmod" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "fmodf" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "fmodl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  (* GNU FUNCTION *)
  |> ApiMap.add "_IO_getc" { arg_typs = [ Skip ]; ret_typ = tainted_v }
  |> ApiMap.add "__errno_location" { arg_typs = []; ret_typ = int_arr }
  |> ApiMap.add "socket" { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "access" { arg_typs = [ Skip; Skip ]; ret_typ = ones }
  |> ApiMap.add "chown" { arg_typs = [ Skip; Skip; Skip ]; ret_typ = ones }
  |> ApiMap.add "uname" { arg_typs = [ Skip ]; ret_typ = ones }
  |> ApiMap.add "mkdir" { arg_typs = [ Skip; Skip ]; ret_typ = ones }
  |> ApiMap.add "mkfifo" { arg_typs = [ Skip; Skip ]; ret_typ = ones }
  |> ApiMap.add "setgroups" { arg_typs = [ Skip; Skip ]; ret_typ = ones }
  |> ApiMap.add "seteuid" { arg_typs = [ Skip ]; ret_typ = ones }
  |> ApiMap.add "setegid" { arg_typs = [ Skip ]; ret_typ = ones }
  |> ApiMap.add "getgid" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "getegid" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "htonl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "htons" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "ntohl" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "ntohs" { arg_typs = [ v_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "pipe" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "time" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "ctime" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "drand48" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "rand" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "random" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "cuserid" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "getlogin" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "getlogin_r" { arg_typs = [ Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "getpid" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "stat" { arg_typs = [ Skip; StructPtr ]; ret_typ = ones }
  |> ApiMap.add "fstat" { arg_typs = [ Skip; StructPtr ]; ret_typ = ones }
  |> ApiMap.add "lstat" { arg_typs = [ Skip; StructPtr ]; ret_typ = ones }
  |> ApiMap.add "strdup" { arg_typs = [ arr_src ]; ret_typ = AllocDst }
  |> ApiMap.add "xstrdup" { arg_typs = [ arr_src ]; ret_typ = AllocDst }
  |> ApiMap.add "xmlStrdup" { arg_typs = [ arr_src ]; ret_typ = AllocDst }
  |> ApiMap.add "g_strdup" { arg_typs = [ arr_src ]; ret_typ = AllocDst }
  |> ApiMap.add "waitpid" { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "getrlimit" { arg_typs = [ Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "pthread_create"
       { arg_typs = [ Skip; Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "pthread_getspecific"
       { arg_typs = [ Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "re_match"
       { arg_typs = [ Skip; Skip; Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "re_search"
       { arg_typs = [ Skip; Skip; Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "setsockopt"
       { arg_typs = [ Skip; Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "system" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "setlocale" { arg_typs = [ Skip; Skip ]; ret_typ = int_v }
  (* Some int_v can be modified to 'ones' *)
  (* Linux File IO *)
  |> ApiMap.add "fopen" { arg_typs = [ Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "lseek" { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "ftell" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "pclose" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "_IO_getc" { arg_typs = [ Skip ]; ret_typ = tainted_v }
  |> ApiMap.add "getchar" { arg_typs = []; ret_typ = tainted_v }
  |> ApiMap.add "getc" { arg_typs = [ Skip ]; ret_typ = tainted_v }
  |> ApiMap.add "read" { arg_typs = [ Skip; buf; Size ]; ret_typ = SizeArg }
  |> ApiMap.add "fread"
       { arg_typs = [ buf; Skip; Size; Skip ]; ret_typ = SizeArg }
  |> ApiMap.add "write"
       { arg_typs = [ Skip; arr_src; Size ]; ret_typ = SizeArg }
  |> ApiMap.add "fwrite"
       { arg_typs = [ arr_src; Skip; Size; Skip ]; ret_typ = SizeArg }
  |> ApiMap.add "recv"
       { arg_typs = [ Skip; buf; Size; Skip ]; ret_typ = SizeArg }
  |> ApiMap.add "send"
       { arg_typs = [ Skip; arr_src; Size; Skip ]; ret_typ = SizeArg }
  |> ApiMap.add "nl_langinfo" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "readlink"
       { arg_typs = [ arr_src; dst; Size ]; ret_typ = int_v }
  |> ApiMap.add "open" { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "close" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "unlink" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "select"
       { arg_typs = [ Skip; Skip; Skip; Skip; Skip ]; ret_typ = int_v }
  |> ApiMap.add "getenv" { arg_typs = [ Skip ]; ret_typ = tainted_arr }
  (* etc *)
  |> ApiMap.add "scanf" { arg_typs = [ Skip; buf_va ]; ret_typ = int_v }
  |> ApiMap.add "fscanf" { arg_typs = [ Skip; Skip; buf_va ]; ret_typ = int_v }
  |> ApiMap.add "sscanf"
       { arg_typs = [ arr_src; Skip; dst_va ]; ret_typ = int_v }
  |> ApiMap.add "fgets" { arg_typs = [ buf; Size; Skip ]; ret_typ = BufArg }
  |> ApiMap.add "fgetc" { arg_typs = [ Skip ]; ret_typ = tainted_v }
  |> ApiMap.add "sprintf"
       { arg_typs = [ dst; Skip; arr_src_va ]; ret_typ = int_v }
  |> ApiMap.add "snprintf"
       { arg_typs = [ dst; Size; Skip; arr_src_va ]; ret_typ = int_v }
  |> ApiMap.add "vsnprintf"
       { arg_typs = [ dst; Size; Skip; arr_src_va ]; ret_typ = int_v }
  |> ApiMap.add "asprintf"
       { arg_typs = [ dst_alloc; Skip; arr_src_va ]; ret_typ = int_v }
  |> ApiMap.add "vasprintf"
       { arg_typs = [ dst_alloc; Skip; arr_src_va ]; ret_typ = int_v }
  |> ApiMap.add "atoi" { arg_typs = [ arr_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "atof" { arg_typs = [ arr_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "atol" { arg_typs = [ arr_src ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "strtod"
       { arg_typs = [ arr_src; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "strtol"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "strtoul"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "strtoimax"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "strtoumax"
       { arg_typs = [ arr_src; Skip; Skip ]; ret_typ = TopWithSrcTaint }
  |> ApiMap.add "fork" { arg_typs = []; ret_typ = int_v }
  |> ApiMap.add "gettext" { arg_typs = [ Skip ]; ret_typ = int_arr }
  |> ApiMap.add "ngettext"
       { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_arr }
  |> ApiMap.add "dgettext" { arg_typs = [ Skip; Skip ]; ret_typ = int_arr }
  |> ApiMap.add "dcgettext"
       { arg_typs = [ Skip; Skip; Skip ]; ret_typ = int_arr }
  |> ApiMap.add "mktime" { arg_typs = [ Skip ]; ret_typ = int_v }
  |> ApiMap.add "localtime" { arg_typs = [ Skip ]; ret_typ = AllocStruct }
  |> ApiMap.add "ctime" { arg_typs = [ Skip ]; ret_typ = int_arr }
  |> ApiMap.add "gmtime" { arg_typs = [ v_src ]; ret_typ = AllocStruct }
  |> ApiMap.add "timegm" { arg_typs = [ arr_src ]; ret_typ = TopWithSrcTaint }
  (* libssh *)
  |> ApiMap.add "_ssh_buffer_unpack"
       { arg_typs = [ arr_src; Skip; Skip; dst_va ]; ret_typ = int_v }
  |> ApiMap.add "g_get_num_processors" { arg_typs = []; ret_typ = int_v }
  (* patron experiment *)
  |> ApiMap.add "TIFFGetField"
       { arg_typs = [ Skip; Skip; buf_va ]; ret_typ = int_v }
