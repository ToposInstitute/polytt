open Core
open Tactic

val formation : Chk.tac -> Chk.tac -> Chk.tac
val intro : Chk.tac -> Chk.tac -> Chk.tac
val lam : ?name:Ident.t -> (Var.tac -> Chk.tac) -> Chk.tac
val base : Syn.tac -> Chk.tac -> Syn.tac
