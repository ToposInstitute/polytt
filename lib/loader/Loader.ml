open Errors
open Parser
open Vernacular

module Terminal = Asai_unix.Make(Code)

type env = { manager : Bantorra.Manager.t; lib : Bantorra.Manager.library }

module Eff = Algaeff.Reader.Make (struct type nonrec env = env end)

let parse_file path =
  let lexbuf = Lexing.from_channel (open_in path) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  try Grammar.commands Lex.token lexbuf with
  | Lex.SyntaxError tok ->
    Logger.fatalf ~loc:(Span.of_lex lexbuf) `LexError {|Unrecognized token "%s"|} (String.escaped tok)
  | Grammar.Error ->
    Logger.fatalf ~loc:(Span.of_lex lexbuf) `ParseError "Failed to parse"

let load_file (unitpath : Bantorra.Manager.path) =
  let env = Eff.read () in
  let (_, _, fpath) = Bantorra.Manager.resolve env.manager env.lib unitpath ~suffix:".poly" in
  let path = Bantorra.FilePath.to_string fpath in
  parse_file path

let initialize_bantorra path =
  let open Bantorra in
  let router = 
    Router.dispatch @@
    function
    | "file" -> Option.some @@
      Router.file ?relative_to:(Router.get_starting_dir ()) ~expanding_tilde:true
    | _ -> None
  in
  let manager = Manager.init ~version:"1.0.0" ~anchor:"polytt-lib" router in
  (* FIXME: Actually load important stuff! *)
  let dir = FilePath.parent @@ FilePath.of_string ~relative_to:(File.get_cwd ()) path in
  let lib, _ = Manager.load_library_from_dir manager dir in
  { manager; lib }

let load path debug =
  Logger.run ~emit:Terminal.display ~fatal:Terminal.display @@ fun () ->
  Logger.wrap (Asai.Diagnostic.map (fun _ -> `LoadFailure)) Bantorra.Error.run @@ fun () ->
  let env = initialize_bantorra path in
  Eff.run ~env @@ fun () ->
  let cmds = parse_file path in
  Driver.execute ~load:load_file ~debug cmds;
