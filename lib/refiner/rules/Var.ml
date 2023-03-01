open Core
open Errors
open Tactic

let local (cell : Cell.t) =
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
