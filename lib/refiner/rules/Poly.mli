open Tactic

val formation : Chk.tac
val intro : Chk.tac -> Chk.tac -> Chk.tac
val base : Syn.tac -> Syn.tac
val fib : Syn.tac -> Chk.tac -> Syn.tac
