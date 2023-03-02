{
open Lexing
open Grammar

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1
    }

let make_table num elems =
  let table = Hashtbl.create num in
  List.iter (fun (k, v) -> Hashtbl.add table k v) elems;
  table

let commands =
  make_table 0 [
    ("#fail", FAIL);
    ("#normalize", NORMALIZE);
    ("#print", PRINT);
    ("#debug", DEBUG);
    ("#quit", QUIT);
  ]

let keywords =
  make_table 0 [
    ("def", DEF);
    ("Type", TYPE);
    ("Poly", POLY);
    ("base", BASE);
    ("fib", FIB);
    ("ℕ", NAT);
    ("zero", ZERO);
    ("succ", SUCC);
    ("elim", NAT_ELIM);
    ("fst", FST);
    ("snd", SND);
  ]

(* Some Lexing Utilities *)
type span =
  {start : position;
   stop : position}

let last_token lexbuf =
  let tok = lexeme lexbuf in
  if tok = "" then None else Some tok

let current_span lexbuf =
  {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p}

}

let line_ending
  = '\r'
  | '\n'
  | "\r\n"
let whitespace =
  [' ' '\t']+

let atom_initial =
  [^ '0'-'9' '-'     '?' '!' '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' '`' ' ' '\t' '\n' '\r']

let atom_subsequent =
  [^                         '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"'     ' ' '\t' '\n' '\r']
let atom = atom_initial atom_subsequent*

let number =
  ['0'-'9']+

let type =
  "Type" number

(* Whitespace/comments *)
rule line_comment kont = parse
  | line_ending
    { new_line lexbuf; kont lexbuf }
  | _
    { line_comment kont lexbuf }

and skip_whitespace kont = parse
  | "--"
    { line_comment (skip_whitespace kont) lexbuf }
  | line_ending
    { new_line lexbuf; (skip_whitespace kont) lexbuf }
  | whitespace
    { skip_whitespace kont lexbuf }
  | ""
    { kont lexbuf }

and token = parse "" { skip_whitespace real_token lexbuf }

and real_token = parse
  (* Symbols *)
  | "λ"
    { LAMBDA }
  | "let"
    { LET }
  | "in"
    { IN }
  | "forall" | "∀"
    { FORALL }
  | "->" | "→"
    { RIGHT_ARROW }
  | "=>" | "⇒"
    { RIGHT_THICK_ARROW }
  | "." | "∘"
    { CIRC }
  | "~>" | "⇝"
    { RIGHT_SQUIGGLY_ARROW }
  | "<~" | "⇜"
    { LEFT_SQUIGGLY_ARROW }
  | ">-" | "⤚"
    { RIGHT_ARROW_TAIL }
  | "*" | "×"
    { TIMES }
  | ':'
     { COLON }
  | ';'
     { SEMICOLON }
  | "::"
    { COLON_COLON }
  | '_'
    { UNDERSCORE }
  | ":="
    { COLON_EQUALS }
  | ","
    { COMMA }
  | "#"
    { HASH }
  | "="
    { EQUALS }
  | "?"
    { QUESTION }
  (* Delimiters *)
  | '('
    { LPR }
  | ')'
    { RPR }
  | '['
    { LSQ }
  | ']'
    { RSQ }
  | '{'
    { LBR }
  | '}'
    { RBR }
  | number
    { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | "on"
    { FLAG true }
  | "off"
    { FLAG false }
  | "#" atom_subsequent+
    {
      let input = lexeme lexbuf in
      match Hashtbl.find commands input with
      | tok -> tok
      | exception Not_found -> Printf.eprintf "Unknown Command: %s\n" (lexeme lexbuf); token lexbuf
    }
  | "." atom
    { LABEL (lexeme lexbuf) }
  | atom
    {
      let input = lexeme lexbuf in
      match Hashtbl.find keywords input with
      | tok -> tok
      | exception Not_found -> Grammar.ATOM input
    }
  | eof
    { EOF }
  | _
    { raise @@ SyntaxError (lexeme lexbuf) }
