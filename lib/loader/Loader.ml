open Errors
open Parser
open Vernacular

module Terminal = Asai_unix.Make(Code)

let load path debug =
  Logger.run ~emit:Terminal.display ~fatal:Terminal.display @@ fun () ->
  let lexbuf = Lexing.from_channel (open_in path) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let cmds =
    try Grammar.commands Lex.token lexbuf with
    | Lex.SyntaxError tok ->
      Logger.fatalf ~loc:(Span.of_lex lexbuf) `LexError {|Unrecognized token "%s"|} (String.escaped tok)
    | Grammar.Error ->
      Logger.fatalf ~loc:(Span.of_lex lexbuf) `ParseError "Failed to parse"
  in
  Driver.execute debug cmds;
  Format.printf "All Done!@."
