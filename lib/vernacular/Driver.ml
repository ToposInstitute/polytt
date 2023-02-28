module CS = Syntax
module D = Core.Domain
module S = Core.Syntax
module Sem = Core.Semantics

open Core

open Elab

exception Quit

let execute_cmd  (cmd : CS.cmd) =
  match cmd.node with
  | CS.Def {name; tp = Some tp; tm} ->
    let tp = Elaborator.chk tp D.Univ in
    let vtp = Sem.eval_top tp in
    let tm = Elaborator.chk tm vtp in
    let vtm = Sem.eval_top tm in
    Debug.print "Defined %a : %a := %a@."
      Ident.pp name
      S.pp_toplevel tp
      S.pp_toplevel (Quote.quote_top ~tp:vtp vtm)
  | CS.Def {name; tp = None; tm} ->
    let (vtp, tm) = Elaborator.syn tm in
    let tp = Quote.quote_top ~tp:D.Univ vtp in
    Debug.print "Defined %a : %a := %a@."
      Ident.pp name
      S.pp_toplevel tp
      S.pp_toplevel tm
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
    let (tp, tm) = Elaborator.syn tm in
    let ntm = Quote.quote_top ~tp:tp (Sem.eval_top tm) in
    Debug.print "Normal Form: %a@."
      S.pp_toplevel ntm
  | CS.Print tm ->
    let (vtp, tm) = Elaborator.syn tm in
    let tp = Quote.quote_top ~tp:D.Univ vtp in
    Debug.print "%a : %a@."
      S.pp_toplevel tm
      S.pp_toplevel tp
  | CS.Debug b ->
    Debug.debug_mode b
  | CS.Quit ->
    raise Quit


let execute (debug : bool) cmds =
  Debug.debug_mode debug;
  try
    List.iter execute_cmd cmds
  with Quit -> ()
