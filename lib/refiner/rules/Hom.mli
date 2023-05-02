open Core
open Tactic

val formation : Chk.tac -> Chk.tac -> Syn.tac
val intro : ?pos_name:Ident.t -> ?neg_name:Ident.t
  -> (Var.tac -> NegVar.tac -> Hom.tac)
  -> Chk.tac
val elim : Syn.tac -> Chk.tac -> Syn.tac

val neg_ap : NegChk.tac -> Syn.tac -> NegSyn.tac
val drop : NegChk.tac

val pos_let : ?name:Ident.binder -> Syn.tac -> (Var.tac -> Hom.tac) -> Hom.tac
val neg_let : ?name:Ident.binder -> NegSyn.tac -> (NegVar.tac -> Hom.tac) -> Hom.tac

val set : Chk.tac -> NegSyn.tac -> Hom.tac -> Hom.tac
val ap : Chk.tac -> NegChk.tac
  -> Syn.tac
  -> ?pos_name:Ident.t -> ?neg_name:Ident.t
  -> (Var.tac -> NegVar.tac -> Hom.tac)
  -> Hom.tac
val done_ : Chk.tac -> NegChk.tac -> Hom.tac
