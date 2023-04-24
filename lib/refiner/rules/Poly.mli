open Core
open Tactic

val formation : Chk.tac
val intro : ?name:Ident.t -> Chk.tac -> (Var.tac -> Chk.tac) -> Chk.tac
val base : Chk.tac -> Syn.tac
val fib : Chk.tac -> Chk.tac -> Syn.tac
