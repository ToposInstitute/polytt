open Core
open Tactic

val formation : ?name:Ident.t -> Chk.tac -> (Var.tac -> Chk.tac) -> Syn.tac
val intro : NegChk.tac -> ?name:Ident.t -> (Var.tac -> NegChk.tac) -> NegChk.tac
val elim : NegSyn.tac
  -> Chk.tac
  -> ?a_name:Ident.t -> ?b_name:Ident.t
  -> (NegVar.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
