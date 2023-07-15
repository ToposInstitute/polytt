open Core
open Tactic

val formation : ?names:Ident.binder list -> Chk.tac -> (Var.tac list -> Chk.tac) -> Syn.tac
val intro : ?name:Ident.binder -> (Var.tac -> Chk.tac) -> Chk.tac
val intro_syn : ?name:Ident.binder -> Chk.tac -> (Var.tac -> Syn.tac) -> Syn.tac
val ap : Syn.tac -> Chk.tac -> Syn.tac
