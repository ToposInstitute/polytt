(** {1 Identifiers} This module defines Identifiers, equality
    check on Identifiers, and pretty printing of identifiers. *)

type path = Yuujinchou.Trie.path

(** The Type of Identifiers. *)
type t = [ `Anon | `User of path | `Machine of int ]

(** The functor of pattern trees, used for binders *)
type 'a pat =
  | Var of 'a
  | Tuple of 'a pat * 'a pat

val over_pat : ('a -> 'b) -> 'a pat -> 'b pat

val choose : t pat -> t

type binder = t pat

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
