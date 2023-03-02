include Elab.Syntax
open Core

type cmd = cmd_ node
and cmd_ =
  | Def of { name : Ident.t; tp : t option; tm : t }
  | Import of { shadowing : bool; unitpath : string list }
  | Fail of { name: Ident.t; tp : t option; tm : t }
  | Normalize of t
  | Print of t
  | Debug of bool
  | Quit
