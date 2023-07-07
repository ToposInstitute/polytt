open Core
open Tactic

val intro : NegChk.tac -> ?name:Ident.binder -> (Var.tac -> NegChk.tac) -> NegChk.tac
val intro_simple : NegSyn.tac -> NegSyn.tac -> NegSyn.tac
val elim : NegSyn.tac
  -> ?a_name:Ident.binder -> ?b_name:Ident.binder
  -> (_ -> Hom.tac)
  -> Hom.tac
