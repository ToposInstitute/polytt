open Tactic

let intro x_tac ?(name = `Anon) y_tac =
  NegChk.rule @@
  function
  | D.Sigma (_, a, b) ->
    let x = NegChk.run x_tac a in
    let y =
      Var.abstract ~name a @@ fun a_plus ->
      NegChk.run (y_tac a_plus) (inst_clo b (Var.value a_plus))
    in
    fun v -> x (do_fst v); y (do_snd v)
  | tp ->
    Error.type_error tp "negative sigma."

let intro_simple x_tac y_tac =
  NegSyn.rule @@ fun () ->
  let x_tp, x = NegSyn.run x_tac in
  Var.abstract x_tp @@ fun _ ->
  let y_tp, y = NegSyn.run y_tac in
  let tp =
    graft_value @@
    Graft.value x_tp @@ fun x_tp ->
    Graft.value y_tp @@ fun y_tp ->
    Graft.build @@
    TB.sigma x_tp @@ fun _ -> y_tp
  in
  tp, fun v -> x (do_fst v); y (do_snd v)

let rec_ scrut_tac ?(a_name = `Anon) ?(b_name = `Anon) case_tac =
  Hom.rule @@ fun q ->
  let scrut_tp, scrut = NegSyn.run scrut_tac in
  match scrut_tp with
  | D.Sigma (_, a, b) ->
    begin
      match inst_const_clo ~tp:a b with
      | Some b ->
        NegVar.abstract ~name:a_name a @@ fun a_neg ->
        NegVar.abstract ~name:b_name b @@ fun b_neg ->
        scrut (D.Pair (NegVar.borrow a_neg, NegVar.borrow b_neg));
        Hom.run (case_tac a_neg b_neg) q
      | None ->
        Core.Debug.print "Uh oh: %a@." D.dump scrut_tp;
        Error.error `TypeError "Tried to use the rec rule on a dependent negative pair. Try elim instead!"
    end
  | _ ->
    Error.error `TypeError "Tried to neg pair eliminate something thats not a neg sigma."

let elim scrut_tac pos_tac ?(a_name = `Anon) ?(b_name = `Anon) case_tac =
  Hom.rule @@ fun q ->
  let scrut_tp, scrut = NegSyn.run scrut_tac in
  match scrut_tp with
  | D.Sigma (_, a, b) ->
    Core.Debug.print "Checking pos against %a@." D.dump a;
    let pos = Chk.run pos_tac a in
    NegVar.abstract ~name:a_name a @@ fun a_neg ->
    NegVar.abstract ~name:b_name (inst_clo b (eval pos)) @@ fun b_neg ->
      scrut (D.Pair (NegVar.borrow a_neg, NegVar.borrow b_neg));
    Hom.run (case_tac a_neg b_neg) q
  | _ ->
    Error.error `TypeError "Tried to neg pair eliminate something thats not a neg sigma."
