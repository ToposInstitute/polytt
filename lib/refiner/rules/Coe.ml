open Core
module S = Syntax
module D = Domain

let coe : D.tp -> D.tp -> (S.t -> S.t) = fun actual goal ->
  match actual, goal with
  | D.Repr, D.Poly -> fun tm1 ->
    S.ElRepr tm1
  | _, _ ->
    Eff.equate ~tp:D.Univ actual goal; fun tm1 -> tm1
