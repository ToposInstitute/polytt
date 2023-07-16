open Core

module S = Syntax

let header fname =
  String.make 20 '-' ^ "[" ^ fname ^ "]" ^ String.make 20 '-' ^ "\n"

let rec execute_file cwd fname =
  let abs_fname = Filename.concat cwd fname in
  if String.equal (Filename.extension abs_fname) ".poly" then
    try
      let _ = print_string (header abs_fname) in
      ignore @@ Loader.load abs_fname false;
    with
      e ->
      Format.eprintf "Could not load file %s@." fname;
      raise e
  else if Sys.is_directory abs_fname then
    let polytt_files = Sys.readdir abs_fname in
    Array.sort String.compare polytt_files;
    Array.iter (execute_file abs_fname) polytt_files

let () =
  let polytt_files = Sys.readdir "." in
  Array.sort String.compare polytt_files;
  Array.iter (execute_file ".") polytt_files
