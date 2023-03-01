open Core
open Tactic

val formation : ?name:Ident.t -> Chk.tac -> (Var.tac -> Chk.tac) -> Syn.tac
val intro : Chk.tac -> Chk.tac -> Chk.tac
val fst : Syn.tac -> Syn.tac
val snd : Syn.tac -> Syn.tac
