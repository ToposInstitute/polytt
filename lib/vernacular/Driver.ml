module CS = Syntax
module D = Core.Domain
module S = Core.Syntax
module Sem = Core.Semantics

open Bantorra

open Core

open Elab

exception Quit

let profile f x =
  let start = Unix.gettimeofday () in
  let pre = Gc.allocated_bytes () in
  let res = f x in
  let post = Gc.allocated_bytes () in
  let stop = Unix.gettimeofday () in
  let () = Printf.printf "Allocated Bytes: %f\n%!" (post -. pre) in
  let () = Printf.printf "Execution time: %fs\n%!" (stop -. start) in
  res

let normalize tm =
  let (tp, tm) = Elaborator.syn tm in
  let ntm = Quote.quote_top ~tp:tp (Sem.eval_top tm) in
  Format.printf "Normal Form: %a@."
    S.pp_toplevel ntm

(* Imports *)

module Terminal = Asai_unix.Make(Bantorra.ErrorCode)
let run_bantorra f = Bantorra.Error.run f
    ~emit:Terminal.display ~fatal:(fun d -> Terminal.display d; failwith "error")

(** Get the current working directory. *)
let cwd = run_bantorra File.get_cwd

let router = run_bantorra @@ fun () ->
  Router.dispatch @@
  function
  | "file" -> Option.some @@
    Router.file ?relative_to:(Router.get_starting_dir ()) ~expanding_tilde:true
  | _ -> None


(** Get a library manager. *)
let manager = run_bantorra @@ fun () -> Manager.init ~version:"1.0.0" ~anchor:"polytt-lib" router

(** Load the library where the current directory belongs. *)
let load_current_library ~file = 
  run_bantorra @@ fun () -> Manager.load_library_from_root manager file

let lib = load_current_library ~file:(FilePath.add_unit_seg cwd "stdlib")

(** Resolve the path to a library module *)
let resolve_source_path lib unitpath =
  Bantorra.Manager.resolve manager lib unitpath ~suffix:".poly"

let rec execute_cmd load_file (cmd : CS.cmd) =
  match cmd.node with
  | CS.Def {name; tp = Some tp; tm} ->
    let tp = Sem.eval_top @@ Elaborator.chk tp D.Univ in
    let tm = Sem.eval_top @@ Elaborator.chk tm tp in
    Eff.define name (Def { tm; tp })
  | CS.Def {name; tp = None; tm} ->
    let (tp, tm) = Elaborator.syn tm in
    let tm = Sem.eval_top tm in
    Eff.define name (Def { tm; tp })
  | CS.Import {unitpath; _} ->
    let (_, _, fpath) = run_bantorra @@ fun () ->
      resolve_source_path lib (UnitPath.of_list unitpath) in
    let cmds = load_file (FilePath.to_string fpath) in
    execute_ load_file cmds
  (* raise Quit *)
  | CS.Fail {tp = Some tp; tm; _} ->
    begin
      try
        let tp = Elaborator.chk tp D.Univ in
        let vtp = Sem.eval_top tp in
        let _ = Elaborator.chk tm vtp in
        failwith "FIXME: better error"
      with _ -> ()
    end
  | CS.Fail {tp = None; tm; _} ->
    begin
      let _ = Elaborator.syn tm in
      failwith "FIXME: better error"
    end
  | CS.Normalize tm ->
    profile normalize tm
  | CS.Print tm ->
    let (vtp, tm) = Elaborator.syn tm in
    let tp = Quote.quote_top ~tp:D.Univ vtp in
    Format.printf "%a : %a@."
      S.pp_toplevel tm
      S.pp_toplevel tp
  | CS.Debug b ->
    Debug.debug_mode b
  | CS.Quit ->
    raise Quit

and execute_ load_file cmds =
  match cmds with
  | [] -> ()
  | decl :: decls ->
    execute_cmd load_file decl;
    execute_ load_file decls
(* List.iter (execute_cmd load_file) cmds *)

let execute load_file (debug : bool) cmds =
  Debug.debug_mode debug;
  print_newline ();
  Eff.run @@ fun () ->
  try
    execute_ load_file cmds
  with Quit -> ()
