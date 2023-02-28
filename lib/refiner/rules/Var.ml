open Core
open Eff
open Errors
open Tactic

let resolve nm =
  Syn.rule @@ fun () ->
  lookup_var nm |> function
  | Some x ->
    (x.tp, quote ~tp:x.tp x.value)
  | None ->
    Logger.fatalf `UnboundVariable "Unbound variable %a."
      Ident.pp nm
