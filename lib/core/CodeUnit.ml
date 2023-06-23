type def = { tp : Syntax.t; def : Syntax.t }

type t = { id : int; defs : (def, CCVector.rw) CCVector.t }

let empty id = { id; defs = CCVector.create () }

let add_def nm def code_unit =
  let lvl = CCVector.length code_unit.defs in
  let glbl = { Global.nm; lvl; code_unit = code_unit.id } in
  CCVector.push code_unit.defs def;
  glbl

let get_def (glbl : Global.t) code_unit =
  assert (glbl.code_unit = code_unit.id);
  CCVector.get code_unit.defs glbl.lvl 
