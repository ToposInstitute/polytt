open Tactic

let formation p_tac q_tac =
  Chk.rule @@
  function
  | D.Poly ->
    S.Tri (Chk.run p_tac D.Poly, Chk.run q_tac D.Poly)
  | _ ->
    Error.error `TypeError "Tensor must be in Poly."
