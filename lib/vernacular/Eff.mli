open Core

val define : Ident.t -> Global.t -> unit
val run : (unit -> 'a) -> 'a
