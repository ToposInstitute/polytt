module Cmd = Syntax
open Core

type env =
  { debug : bool;
    load : Bantorra.Manager.path -> Cmd.cmd list
  }

(** Resolve a path and parse the resulting file. *)
val load : Bantorra.Manager.path -> Cmd.cmd list

(** Run the continuation in a fresh code-unit and namespace, and
    then bring all exports into the current namespace. *)
val scoped : (unit -> unit) -> unit

(** Add a top-level definition *)
val define : Ident.t -> Global.t -> unit

val run : env -> (unit -> 'a) -> 'a
