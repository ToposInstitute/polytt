module Cmd = Syntax
open Core

type env =
  { debug : bool;
    load : Bantorra.Manager.path -> Cmd.cmd list
  }

module Eff = Algaeff.Reader.Make (struct type nonrec env = env end)

type empty = |

module Param =
struct
  type data = Global.t
  type tag = unit
  type hook = empty
  type context = empty
end
module Modifier = Yuujinchou.Modifier.Make(Param)
module Scope = Yuujinchou.Scope.Make(Param)(Modifier)

let load path =
  let env = Eff.read () in
  env.load path

let define name defn =
  match name with
  | `User path ->
    Scope.include_singleton (path, (defn, ()))
  | _ ->
    ()

let run env k =
  Debug.debug_mode env.debug;
  Eff.run ~env @@ fun () ->
  Scope.run @@ fun () ->
  let resolve path =
    Scope.resolve path
    |> Option.map fst
  in
  Refiner.Eff.Globals.run ~resolve @@ fun () ->
  Refiner.Eff.Hole.run k
