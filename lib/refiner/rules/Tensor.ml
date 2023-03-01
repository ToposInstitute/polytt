open Tactic

let formation p_tac q_tac =
  Chk.rule @@
  function
  | D.Poly ->
    S.Tensor (Chk.run p_tac D.Poly, Chk.run q_tac D.Poly)
  | _ ->
    Error.error `TypeError "Tensor must be in Poly."

let intro p_tac q_tac =
  Chk.rule @@
  function
  | D.Tensor (p, q) ->
    S.TensorIntro (Chk.run p_tac p, Chk.run q_tac q)
  | _ ->
    Error.error `TypeError "Tensor intro must be in Tensor."

let elim ?(p_name = `Anon) ?(q_name = `Anon) mot_tac bdy_tac scrut_tac =
  Syn.rule @@ fun () ->
  let (scrut_tp, scrut) = Syn.run scrut_tac in
  match scrut_tp with
  | D.Tensor (p, q) ->
    let mot = Chk.run mot_tac D.Poly in
    let vmot = eval mot in
    (* FIXME: Linearity!!! *)
    Var.abstract ~name:p_name p @@ fun p_var ->
    Var.abstract ~name:q_name q @@ fun q_var ->
    let bdy = Chk.run (bdy_tac p_var q_var) vmot in
    vmot, S.TensorElim (mot, bdy, scrut)
  | _ ->
    Error.error `TypeError "Tensor elim must be applied to a tensor."
