open Core
open Tactic

let formation p_tac q_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  let q = Chk.run q_tac D.Poly in
  D.Univ, S.Hom(p, q)

let intro ?(pos_name = `Anon) ?(neg_name = `Anon) (bdy_tac : Var.tac -> NegVar.tac -> Hom.tac) : Chk.tac =
  Chk.rule @@
  function
  | D.Hom (p, q) ->
    let p_base = do_base p in
    let ok =
      Linearity.run @@ fun () ->
      Var.abstract ~name:pos_name p_base @@ fun pos_var ->
      let p_fib = do_fib p (Var.value pos_var) in
      Core.Debug.print "Introducing negated %a@." D.dump p_fib;
      NegVar.abstract ~name:neg_name p_fib @@ fun neg_var ->
      let bdy = Hom.run (bdy_tac pos_var neg_var) q in
      S.HomLam (pos_name, neg_name, bdy)
    in
    begin
      match ok with
      | Some ok -> ok
      | None ->
        Error.error `LinearVariablesNotUsed "Didn't use all your linear variables."
    end
  | _ ->
    Error.error `TypeError "Must do a hom lambda in hom."

let elim hom_tac arg_tac =
  Syn.rule @@ fun () ->
  let hom_tp, hom = Syn.run hom_tac in
  match hom_tp with
  | D.Hom (p, q) ->
    let p_base = Chk.run arg_tac (do_base p) in
    let tp =
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.value (eval p_base) @@ fun p_base ->
      Graft.build @@
      TB.sigma (TB.base q) @@ fun q_base ->
      TB.pi (TB.fib q q_base) @@ fun _ -> TB.fib p p_base
    in
    tp, S.HomElim (hom, p_base)
  | _ ->
    Error.error `TypeError "Tried to eliminate from non-hom."

let neg_ap (neg_tac : NegChk.tac) (fn_tac : Syn.tac) =
  NegSyn.rule @@ fun () ->
  Debug.print "Doing a neg ap@.";
  let fn_tp, fn = Syn.run fn_tac in
  match fn_tp with
  | D.Pi (_, a, clo) ->
    begin
      match inst_const_clo ~tp:a clo with
      | Some b ->
        let neg = NegChk.run neg_tac b in
        Debug.print "b in neg_ap: %a@." S.dump (quote ~tp:D.Univ b);
        Debug.print "%a in neg_ap@." S.dump (quote ~tp:D.Univ a);
        a, S.NegAp (neg, fn)
      | None ->
        Error.error `TypeError "The skolem. He escaped his scope. Yes. YES. The skolem is out."
    end
  | _ ->
    Error.error `TypeError "Must do a neg ap against a function."

let drop : NegChk.tac =
  NegChk.rule @@ fun _ ->
  S.Drop

let set (pos_tac : Syn.tac) (neg_tac : NegChk.tac) (steps_tac : Hom.tac) : Hom.tac =
  Hom.rule @@ fun q ->
  let pos_tp, pos = Syn.run pos_tac in
  let neg = NegChk.run neg_tac pos_tp in
  let steps = Hom.run steps_tac q in
  S.Set (pos, neg, steps)

let ap (pos_tac : Chk.tac) (neg_tac : NegChk.tac)
    (phi_tac : Syn.tac)
    ?(pos_name = `Anon) ?(neg_name = `Anon)
    (steps_tac : Var.tac -> NegVar.tac -> Hom.tac) =
  Hom.rule @@ fun r ->
  let phi_tp, phi = Syn.run phi_tac in
  match phi_tp with
  | D.Hom (p, q) ->
    let pos = Chk.run pos_tac (do_base p) in
    let vpos = eval pos in
    let neg = NegChk.run neg_tac (do_fib p vpos) in
    Var.abstract ~name:pos_name (do_base q) @@ fun pos_var ->
    NegVar.abstract ~name:neg_name (do_fib q (Var.value pos_var)) @@ fun neg_var ->
    let steps = Hom.run (steps_tac pos_var neg_var) r in
    S.HomAp (phi, pos, neg, pos_name, neg_name, steps)
  | _ ->
    Error.error `TypeError "Must ap a hom to a hom!"

(* done is a reserved keyword :) *)
let done_ (pos_tac : Chk.tac) (neg_tac : NegChk.tac) : Hom.tac =
  Hom.rule @@ fun r ->
  let pos = Chk.run pos_tac (do_base r) in
  let neg = NegChk.run neg_tac (do_fib r (eval pos)) in
  S.Done (pos, neg)
