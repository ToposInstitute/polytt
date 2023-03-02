open Errors
open Parser

module Terminal = Asai_unix.Make(Code)

let create_lexbuf path =
  let ch = open_in path in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = path};
  ch, lexbuf

let parse_with_error parser lexbuf =
  try Ok (parser Lex.token lexbuf) with
  | Lex.SyntaxError tok ->
    Logger.fatalf ~loc:(Span.of_lex lexbuf) `LexError {|Unrecognized token "%s"|} (String.escaped tok)
  | Grammar.Error ->
    Logger.fatalf ~loc:(Span.of_lex lexbuf) `ParseError "Failed to parse"

let load_file input =
  let res = ref (Error "Failed to load file") in
  let _ = Logger.run ~emit:Terminal.display ~fatal:Terminal.display @@ fun () ->
    let ch, lexbuf = create_lexbuf input in
    let sign = parse_with_error Grammar.commands lexbuf in
    close_in ch;
    res := sign in
  match !res with
  | Ok cmds -> cmds
  | Error e -> failwith e
