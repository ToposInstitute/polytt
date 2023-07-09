open Core
open Tactic

val formation : ?names:Ident.binder list -> Chk.tac -> (Var.tac list -> Chk.tac) -> Syn.tac
val intro : ?name:Ident.binder -> (Var.tac -> Chk.tac) -> Chk.tac
val ap : Syn.tac -> Chk.tac -> Syn.tac
