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
  let () = Debug.print "Allocated Bytes: %f\n%!" (post -. pre) in
  let () = Debug.print "Execution time: %fs\n%!" (stop -. start) in
  res

let normalize tm =
  let (tp, tm) = Elaborator.syn tm in
  let ntm = Quote.quote_top ~tp:tp (Sem.eval_top tm) in
  Format.printf "Normal Form: %a@."
    S.pp_toplevel ntm

let rec execute_cmd  (cmd : CS.cmd) =
  match cmd.node with
  | CS.Def {name; tp = Some tp; tm} ->
    Debug.print "-------------------------------------------------@.";
    Debug.print "> Elaborating %a@." Ident.pp name;
    Debug.print "-------------------------------------------------@.";
    let tp = Sem.eval_top @@ Elaborator.chk tp D.Univ in
    let value = Sem.eval_top @@ Elaborator.chk tm tp in
    let glbl = CodeUnit.add_def name { tp; value } in
    Eff.define name glbl
  | CS.Def {name; tp = None; tm} ->
    let (tp, tm) = Elaborator.syn tm in
    let value = Sem.eval_top tm in
    let glbl = CodeUnit.add_def name { tp; value } in
    Eff.define name glbl
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
  | CS.Import {shadowing; unitpath} ->
    let cmds = Eff.load (UnitPath.of_list unitpath) in
    Eff.scoped @@ fun () ->
    List.iter execute_cmd cmds
  | CS.Normalize tm ->
    profile normalize tm
  | CS.Print tm ->
    let (vtp, tm) = Elaborator.syn tm in
    Debug.print "Preprint: %a@." S.dump tm;
    let tp = Quote.quote_top ~tp:D.Univ vtp in
    Format.printf "%a : %a@."
      (* FIXME may not be correct precedence *)
      (S.pp { pos = Emp; neg_size = 0; neg = Emp } (Precedence.left_of S.juxtaposition)) tm
      S.pp_toplevel tp
  | CS.Debug b ->
    Debug.debug_mode b
  | CS.Quit ->
    raise Quit

let execute ~load ?(debug = false) cmds =
  print_newline ();
  Eff.run { debug; load } @@ fun () ->
  try
    CodeUnit.with_new_unit @@ fun () ->
    List.iter execute_cmd cmds
  with Quit -> ()
