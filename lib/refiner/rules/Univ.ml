open Errors
open Tactic

let formation = Chk.rule @@
  function
  | D.Univ -> S.Univ (* type is in type. *)
  | _ ->
    Logger.fatalf `TypeError "Expected element of type."
