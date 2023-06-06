open Core

module S = Syntax

let header fname =
  String.make 20 '-' ^ "[" ^ fname ^ "]" ^ String.make 20 '-' ^ "\n"

let execute_file fname =
  if String.equal (Filename.extension fname) ".cooltt" then
    try
      let _ = print_string (header fname) in
      ignore @@ Loader.load fname false;

      Format.eprintf "loaded file %s@." fname;
    with
      e ->
      Format.eprintf "Could not load file %s@." fname;
      raise e

let () =
  let polytt_files = Sys.readdir "." in
  Array.sort String.compare polytt_files;
  Array.iter execute_file polytt_files
