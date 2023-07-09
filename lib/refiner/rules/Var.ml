open Core
open Tactic
open Ident

let local (cell : Cell.pos) =
  Syn.rule @@ fun () ->
  (cell.tp, quote ~tp:cell.tp cell.value)

let global res =
  Syn.rule @@ fun () ->
  match res with
  | Globals.Def {tp; tm} ->
    tp, quote ~tp:tp tm

let let_bind ?(name = Var `Anon) (tm : Syn.tac) (f : Var.tac -> Chk.tac) =
  Chk.rule @@ fun rtp ->
  let (vtp, etm) = Syn.run tm in
  let vtm = Eff.eval etm in
  let body = Chk.run (Var.concrete ~name vtp vtm f) rtp in
  Let (Var.choose name, etm, body)

let negative (cell : Cell.neg) =
  NegSyn.rule @@ fun () ->
  match Eff.Locals.consume_neg cell.lvl () with
  | None ->
    Error.error `LinearVariableDoubleUse "Linear variable already used: %a." Ident.pp cell.name
  | Some writer ->
    Debug.print "marking %a@." Ident.pp cell.name;
    (cell.tp, fun v ->
      Debug.print "writing %a <- %a@." Ident.pp cell.name D.dump v;
      writer v)
