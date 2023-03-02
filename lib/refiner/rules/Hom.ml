open Tactic

let formation p_tac q_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  let q = Chk.run q_tac D.Poly in
  D.Univ, S.Hom(p, q)
