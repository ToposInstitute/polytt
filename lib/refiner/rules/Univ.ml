open Errors
open Tactic

let formation = Syn.rule @@ fun () ->
  (D.Univ, S.Univ) (* type is in type. *)
