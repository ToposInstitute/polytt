(** {1 Identifiers} This module defines Identifiers, equality
    check on Identifiers, and pretty printing of identifiers. *)

type path = Yuujinchou.Trie.path

(** The Type of Identifiers. *)
type t = [ `Anon | `User of path | `Machine of int ]

(** Construct an anonymous Identifier. This is used for underscores. *)
val anon : t

(** Construct a user defined Identifier. *)
val user : path -> t

(** Construct a machine defined Identifier. *)
val machine : int -> t

(** Equality check for Identifiers *)
val equal : t -> t -> bool

(** Pretty print a qualified identifier *)
val pp_path : Format.formatter -> path -> unit

(** Pretty print a qualified identifier *)
val pp : Format.formatter -> t -> unit
