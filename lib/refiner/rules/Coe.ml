open Core
module S = Syntax
module D = Domain

let coe : S.t -> D.tp -> D.tp -> S.t = fun tm1 actual goal ->
  match actual, goal with
  | D.Repr, D.Poly ->
    S.PolyIntro (`Anon, S.FinSet ["unit"], S.shift (S.Log tm1))
  | _, _ ->
    Eff.equate ~tp:D.Univ actual goal; tm1

