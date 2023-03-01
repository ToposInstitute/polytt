open Core
open Tactic

val formation : ?name:Ident.t -> Chk.tac -> (Var.tac -> Chk.tac) -> Syn.tac
val intro : ?name:Ident.t -> (Var.tac -> Chk.tac) -> Chk.tac
val ap : Syn.tac -> Chk.tac -> Syn.tac
