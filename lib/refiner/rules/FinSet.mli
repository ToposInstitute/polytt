open Tactic

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

val formation : labelset -> Syn.tac
val label : label -> Chk.tac
val record : Chk.tac labeled -> Syn.tac
val record_lit : Chk.tac labeled -> Chk.tac
