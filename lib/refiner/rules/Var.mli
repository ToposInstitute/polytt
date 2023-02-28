open Core
open Tactic

val local : Cell.t -> Syn.tac
val global : Globals.resolved -> Syn.tac
