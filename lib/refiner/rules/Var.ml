open Tactic
open Eff

let resolve nm =
  Syn.rule @@ fun () ->
  lookup_var nm |> function
  | Some x -> (x.tp, quote ~tp:x.tp x.value)
  | None -> failwith "FIXME: Unbound Variable, Better Errors!!"
