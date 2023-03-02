module CS := Syntax

val execute : (string -> Syntax.cmd list) -> bool -> CS.cmd list -> unit
