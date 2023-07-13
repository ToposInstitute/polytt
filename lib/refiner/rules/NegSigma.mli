open Core
open Tactic

val intro : NegChk.tac -> ?name:Ident.binder -> (Var.tac -> NegChk.tac) -> NegChk.tac
val intro_simple : NegSyn.tac -> NegSyn.tac -> NegSyn.tac
val intro_simple_chk : NegChk.tac -> NegChk.tac -> NegChk.tac
val elim : NegSyn.tac
  -> ?a_name:Ident.binder -> ?b_name:Ident.binder
  -> (NegVar.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
