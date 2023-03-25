open Core
open Tactic

val intro : NegChk.tac -> ?name:Ident.t -> (Var.tac -> NegChk.tac) -> NegChk.tac
val intro_simple : NegSyn.tac -> NegSyn.tac -> NegSyn.tac
val rec_ : NegSyn.tac
  -> ?a_name:Ident.t -> ?b_name:Ident.t
  -> (NegVar.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
val elim : NegSyn.tac
  -> Chk.tac
  -> ?a_name:Ident.t -> ?b_name:Ident.t
  -> (NegVar.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
