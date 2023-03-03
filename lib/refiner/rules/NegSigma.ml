open Tactic

let formation ?(name = `Anon) base_tac fam_tac =
  Syn.rule @@ fun () ->
  let base = Chk.run base_tac D.Univ in
  let vbase = eval base in
  let fam = Var.abstract ~name vbase @@ fun arg ->
    Chk.run (fam_tac arg) D.NegUniv
  in D.NegUniv, S.NegSigma (name, base, fam)

let intro x_tac ?(name = `Anon) y_tac =
  NegChk.rule @@
  function
  | D.NegSigma (_, a, b) ->
    let x = NegChk.run x_tac (do_negate a) in
    let y =
      Var.abstract ~name a @@ fun a_plus ->
      NegChk.run (y_tac a_plus) (inst_clo b (Var.value a_plus))
    in
    S.NegPair (x, name, y)
  | _ ->
    Error.error `TypeError "Tried to introduce a neg pair into something thats not a neg sigma."

let elim scrut_tac pos_tac ?(a_name = `Anon) ?(b_name = `Anon) case_tac =
  Hom.rule @@ fun q ->
  let scrut_tp, scrut = NegSyn.run scrut_tac in
  match scrut_tp with
  | D.NegSigma (_, a, b) ->
    let pos = Chk.run pos_tac a in
    NegVar.abstract ~name:a_name (do_negate a) @@ fun a_neg ->
    NegVar.abstract ~name:b_name (inst_clo b (eval pos)) @@ fun b_neg ->
    let case = Hom.run (case_tac a_neg b_neg) q in
    S.Unpack { scrut; pos; a_name; b_name; case }
  | _ ->
    Error.error `TypeError "Tried to neg pair eliminate something thats not a neg sigma."
