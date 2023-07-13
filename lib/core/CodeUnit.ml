type def = { tp : Domain.t; value : Domain.t }
type code_unit = (def, CCVector.rw) CCVector.t

type env = { current: int; code_units : (code_unit, CCVector.rw) CCVector.t }

module Eff = Algaeff.Reader.Make (struct type nonrec env = env end)

let with_new_unit k =
  let env = Eff.read () in
  let id = CCVector.length env.code_units in
  let code_unit = CCVector.create () in
  CCVector.push env.code_units code_unit;
  Eff.scope (fun env -> { env with current = id }) k

let current_code_unit () =
  let env = Eff.read () in
  CCVector.get env.code_units env.current, env.current

let add_def nm def =
  let code_unit, id = current_code_unit () in
  let lvl = CCVector.length code_unit in
  let glbl = { Global.nm; lvl; code_unit = id } in
  CCVector.push code_unit def;
  glbl

let get_def (glbl : Global.t) =
  let env = Eff.read () in
  let code_unit = CCVector.get env.code_units glbl.code_unit in
  CCVector.get code_unit glbl.lvl

let get_def_value glbl =
  let def = get_def glbl in
  def.value

let get_def_tp glbl =
  let def = get_def glbl in
  def.tp

let run k =
  let code_units = CCVector.create () in
  Eff.run ~env:{ current = 0; code_units } k
