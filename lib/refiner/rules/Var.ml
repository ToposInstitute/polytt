open Core
open Tactic

let local (cell : Cell.pos) =
  Syn.rule @@ fun () ->
  (cell.tp, quote ~tp:cell.tp cell.value)

let global res =
  Syn.rule @@ fun () ->
  match res with
  | Globals.Def {tp; tm} ->
    tp, quote ~tp:tp tm

let let_bind ?(name = `Anon) (tm : Syn.tac) (f : Var.tac -> Chk.tac) =
  Chk.rule @@ fun rtp ->
  let (vtp, etm) = Syn.run tm in
  let vtm = Eff.eval etm in
  let body = Chk.run (Var.concrete ~name vtp vtm f) rtp in
  Let (name, etm, body)

let negative (cell : Cell.neg) =
  NegSyn.rule @@ fun () ->
  match Eff.Locals.consume_neg cell.lvl () with
  | None ->
    Error.error `LinearVariableDoubleUse "Linear variable already used."
  | Some writer ->
    (cell.tp, S.Var cell.lvl, writer)
