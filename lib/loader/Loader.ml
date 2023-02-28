open Parser
open Vernacular

let load path =
  let lexbuf = Lexing.from_channel (open_in path) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let cmds =
    try Grammar.commands Lex.token lexbuf with
    | Lex.SyntaxError tok ->
      failwith "FIXME: parse error"
    | Grammar.Error ->
      failwith "FIXME: parse error"
  in
  Driver.execute cmds;
  Format.printf "All Done!@."
