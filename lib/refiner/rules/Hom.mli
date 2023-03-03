open Core
open Tactic

val formation : Chk.tac -> Chk.tac -> Syn.tac
val intro : ?pos_name:Ident.t -> ?neg_name:Ident.t
  -> (Var.tac -> NegVar.tac -> Hom.tac)
  -> Chk.tac
val elim : Syn.tac -> Chk.tac -> Syn.tac

val neg_ap : NegChk.tac -> Syn.tac -> NegSyn.tac

val set : Syn.tac -> NegChk.tac -> Hom.tac -> Hom.tac
val ap : Chk.tac -> NegChk.tac
  -> Syn.tac
  -> ?pos_name:Ident.t -> ?neg_name:Ident.t
  -> (Var.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
val done_ : Chk.tac -> NegChk.tac -> Hom.tac
