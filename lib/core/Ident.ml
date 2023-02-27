type path = Yuujinchou.Trie.path
type t = [ `Anon | `User of path | `Machine of int ]

let anon = `Anon
let user parts = `User parts
let machine nm = `Machine nm

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
