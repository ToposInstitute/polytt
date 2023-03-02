open Cmdliner
open Vernacular

let file =
  let doc = "Load and evaluate FILE." in
  let docv = "FILE" in
  Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)

let debug =
  let doc = "Enable debug mode." in
  Arg.(value & flag & info ["debug"] ~doc)

let load path debug =
  let cmds = Loader.load_file path in
  Driver.execute Loader.load_file debug cmds;
  Format.printf "All Done!@."

let load_t = Term.(const load $ file $ debug)

let cmd = Cmd.v (Cmd.info "polytt") load_t

let () = exit (Cmd.eval cmd)
