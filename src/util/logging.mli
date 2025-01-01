type level = DEBUG | INFO | WARN | ERROR

val init : unit -> unit
val finalize : unit -> unit
val set_level : level -> unit
val debug : ?to_consol:bool -> ('a, Format.formatter, unit) format -> 'a

val info :
  ?to_consol:bool -> ?level:int -> ('a, Format.formatter, unit) format -> 'a

val warn : ?to_consol:bool -> ('a, Format.formatter, unit) format -> 'a
val error : ?to_consol:bool -> ('a, Format.formatter, unit) format -> 'a
val report : ?to_consol:bool -> ('a, Format.formatter, unit) format -> 'a
val flush_all : unit -> unit
val dual_formatter : Format.formatter -> Format.formatter -> Format.formatter
