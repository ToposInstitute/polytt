open Core
open Tactic

val formation : ?names:Ident.binder list -> Chk.tac -> (Var.tac list -> Chk.tac) -> Syn.tac
val intro : Chk.tac -> Chk.tac -> Chk.tac
val fst : Syn.tac -> Syn.tac
val snd : Syn.tac -> Syn.tac
