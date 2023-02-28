type path = Yuujinchou.Trie.path

(** The type of identifiers *) 
type t = [ `Anon | `User of path | `Machine of int ]

(** Anonymous names, eg., underscores *)
let anon = `Anon

(** User defined names, potentially qualified *)
let user parts = `User parts

(** Machine generated names *)
let machine nm = `Machine nm

let equal n1 n2 =
  match (n1, n2) with
  | `Anon, `Anon -> true
  | `User path1, `User path2 -> List.equal String.equal path1 path2 
  | `Machine i1, `Machine i2 -> Int.equal i1 i2
  | _ -> false

let pp_path fmt path =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ".")
    Format.pp_print_string
    fmt path

let pp fmt =
  function
  | `Anon -> Format.pp_print_string fmt "_"
  | `Machine n -> Format.fprintf fmt "<%d>" n
  | `User path -> pp_path fmt path
