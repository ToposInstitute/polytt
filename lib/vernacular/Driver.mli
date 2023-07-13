module Cmd := Syntax

val execute : load:(Bantorra.Manager.path -> Cmd.cmd list) -> ?debug:bool -> Cmd.cmd list -> unit
