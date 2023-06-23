(** Names for Top-Level definitions *)

(** A top-level name consists of a user-facing {!type:Ident.t}, a DeBruijn level, along with
    the ID of the code unit that the binding resides in.

    You should never create a {!type:Global.t} by hand; instead, use {!val:CodeUnit.add_def}
    to ensure that global names actually point to a definition. *)
type t = { nm : Ident.t; lvl : int; code_unit : int }

val pp : Format.formatter -> t -> unit
val dump : Format.formatter -> t -> unit
