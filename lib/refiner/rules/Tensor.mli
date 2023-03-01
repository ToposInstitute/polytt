open Core
open Tactic

val formation : Chk.tac -> Chk.tac -> Chk.tac
val intro : Chk.tac -> Chk.tac -> Chk.tac
val elim : ?p_name:Ident.t -> ?q_name:Ident.t
  -> Chk.tac
  -> (Var.tac -> Var.tac -> Chk.tac)
  -> Syn.tac
  -> Syn.tac
