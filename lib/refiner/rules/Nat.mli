open Tactic

val formation : Syn.tac
val zero : Chk.tac
val succ : Chk.tac
val zero_syn : Syn.tac
val succ_syn : Syn.tac
val lit : int -> Chk.tac
val lit_syn : int -> Syn.tac
val elim : Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac -> Syn.tac
