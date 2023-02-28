type path = Yuujinchou.Trie.path
type t = [ `Anon | `User of path | `Machine of int ]

val anon : t
val user : path -> t
val machine : int -> t

val equal : t -> t -> bool

val pp_path : Format.formatter -> path -> unit
val pp : Format.formatter -> t -> unit
