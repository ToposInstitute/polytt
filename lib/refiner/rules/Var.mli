open Core
open Tactic

val local : Cell.pos -> Syn.tac
val global : Globals.resolved -> Syn.tac
val let_bind : ?name:Ident.binder -> Syn.tac -> (Var.tac -> Chk.tac) -> Chk.tac
val negative : Cell.neg -> NegSyn.tac
