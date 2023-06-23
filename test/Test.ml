open Core

module S = Syntax

let header fname =
  String.make 20 '-' ^ "[" ^ fname ^ "]" ^ String.make 20 '-' ^ "\n"

let rec execute_file cwd fname =
  let abs_fname = Filename.concat cwd fname in
  if String.equal (Filename.extension abs_fname) ".poly" then
    try
      let _ = print_string (header fname) in
      ignore @@ Loader.load abs_fname false;
    with
      e ->
      Format.eprintf "Could not load file %s@." fname;
      raise e
  else if Sys.is_directory abs_fname then
    Array.iter (execute_file abs_fname) (Sys.readdir abs_fname)

let () =
  let polytt_files = Sys.readdir "." in
  Array.sort String.compare polytt_files;
  Array.iter (execute_file (Sys.getcwd ())) polytt_files
