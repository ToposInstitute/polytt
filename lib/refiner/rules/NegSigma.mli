open Core
open Tactic

val intro : NegChk.tac -> ?name:Ident.t -> (Var.tac -> NegChk.tac) -> NegChk.tac
val intro_simple : NegSyn.tac -> NegSyn.tac -> NegSyn.tac
val elim : NegSyn.tac
  -> ?a_name:Ident.t -> ?b_name:Ident.t
  -> (_ -> Hom.tac)
  -> Hom.tac
