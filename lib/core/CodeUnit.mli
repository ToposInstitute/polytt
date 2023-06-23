type t

(** A single definition stored in a code-unit. *)
type def = { tp : Syntax.t; def : Syntax.t }

(** Create a new code-unit using the provided ID. *)
val empty : int -> t

(** Add a definition to a code-unit.
    This returns a {!type:Global.t} associated to the new definition. *)
val add_def : Ident.t -> def -> t -> Global.t

(** Look up a definition in a code-unit. *)
val get_def : Global.t -> t -> def
