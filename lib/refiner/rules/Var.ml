open Tactic

let local (cell : Cell.t) =
  Syn.rule @@ fun () ->
  (cell.tp, quote ~tp:cell.tp cell.value)

let global res =
  Syn.rule @@ fun () ->
  match res with
  | Globals.Def {tp; tm} ->
    tp, quote ~tp:tp tm
