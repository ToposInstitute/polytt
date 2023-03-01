open Tactic

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

val formation : labelset -> Chk.tac
val label : label -> Chk.tac
val record : Chk.tac labeled -> Chk.tac
val record_lit : Chk.tac labeled -> Chk.tac
