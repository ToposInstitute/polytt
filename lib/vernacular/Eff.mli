open Core

val define : Ident.t -> Refiner.Eff.Globals.resolved -> unit
val run : (unit -> 'a) -> 'a
