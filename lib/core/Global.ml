type t = { nm : Ident.t; lvl : int; code_unit : int }

let pp fmt glbl = Ident.pp fmt glbl.nm
let dump fmt glbl =
  Format.fprintf fmt "global[%a, %d, %d]" Ident.pp glbl.nm glbl.lvl glbl.code_unit
