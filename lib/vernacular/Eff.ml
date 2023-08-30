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
module Scope = Yuujinchou.Scope.Make(Param)

let load path =
  let env = Eff.read () in
  env.load path

let define name defn =
  match name with
  | `User path ->
    Scope.include_singleton (path, (defn, ()))
  | _ ->
    ()

let resolve path =
  Scope.resolve path
  |> Option.map fst

let scoped k =
  CodeUnit.with_new_unit @@ fun () ->
  (* [HACK: Reed M, 23/06/2023] We need to ensure that the 'resolve' effect is handled
     by the correct effect handler, so we need to wrap this in a redundant
     'Globals.run'. This highlights that so-called "proxy effects"
     (where the effect handler just re-raises another effect, potentially via a call-back) are bad,
     but a better design is somewhat unclear at the moment.. *)
  let exports =
    Scope.run @@ fun () ->
    Refiner.Eff.Globals.run ~resolve @@ fun () ->
    k ();
    Scope.get_export ()
  in Scope.include_subtree ([], exports)

let run env k =
  Debug.debug_mode env.debug;
  CodeUnit.run @@ fun () ->
  Eff.run ~env @@ fun () ->
  Scope.run @@ fun () ->
  Refiner.Eff.Globals.run ~resolve @@ fun () ->
  Refiner.Eff.Hole.run k
