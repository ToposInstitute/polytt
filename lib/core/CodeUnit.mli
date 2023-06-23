(** A single definition stored in a code-unit. *)
type def = { tp : Domain.t; value : Domain.t }

(** Create a new code-unit, and call the provided function
    with that code-unit as the current code-unit. *)
val with_new_unit : (unit -> 'a) -> 'a

(** Add a definition to the current code-unit.
    This returns a {!type:Global.t} associated to the new definition. *)
val add_def : Ident.t -> def -> Global.t

(** Look up a definition. *)
val get_def : Global.t -> def

(** Handle the code-unit effects, starting with no code-units defined. *)
val run : (unit -> 'a) -> 'a
