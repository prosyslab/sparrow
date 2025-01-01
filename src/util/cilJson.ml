module Cil = ProsysCil.Cil

type t = Yojson.Safe.t

let rec of_lhost = function
  | Cil.Var v -> `List [ `String "Var"; `String v.vname ]
  | Cil.Mem e -> `List [ `String "Mem"; of_exp e ]

and of_offset = function
  | Cil.NoOffset -> `Null
  | Cil.Field (f, offset) ->
      `List [ `String "Field"; `String f.fname; of_offset offset ]
  | Cil.Index (e, offset) ->
      `List [ `String "Index"; of_exp e; of_offset offset ]

and of_lval (lhost, offset) = `List [ of_lhost lhost; of_offset offset ]
and of_const = function _ -> `Int 0

and of_exp = function
  | Cil.Const c -> `List [ `String "Const"; of_const c ]
  | Cil.Lval l -> `List [ `String "Lval"; of_lval l ]
  | _ -> `List [ `String "OtherExp" ]

let print oc x = Yojson.Safe.pretty_to_channel oc x
