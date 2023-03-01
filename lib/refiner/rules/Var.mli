open Core
open Tactic

val local : Cell.t -> Syn.tac
val global : Globals.resolved -> Syn.tac
val let_bind : ?name:Ident.t -> Syn.tac -> (Var.tac -> Chk.tac) -> Chk.tac
