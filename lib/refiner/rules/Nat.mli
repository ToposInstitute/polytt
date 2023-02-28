open Tactic

val formation : Chk.tac
val zero: Chk.tac
val succ : Chk.tac -> Chk.tac
val lit : int -> Chk.tac
val elim : Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac -> Syn.tac
