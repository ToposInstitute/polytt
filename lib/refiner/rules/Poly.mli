open Core
open Tactic

val formation : Chk.tac
val repr_formation : Chk.tac
val intro : ?name:Ident.binder -> Chk.tac -> (Var.tac -> Chk.tac) -> Chk.tac
val repr_intro : Chk.tac -> Chk.tac
val base : Chk.tac -> Syn.tac
val fib : Chk.tac -> Chk.tac -> Syn.tac
val log : Chk.tac -> Syn.tac
