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
      Eff.Locals.run_linear @@ fun () ->
      Var.abstract ~name:pos_name p_base @@ fun pos_var ->
      let p_fib = do_fib p (Var.value pos_var) in
      Core.Debug.print "Introducing negated %a@." D.dump p_fib;
      NegVar.abstract ~name:neg_name p_fib @@ fun neg_var ->
      let tail () =
        begin
        let thingy = Eff.Locals.head () in
        let q = quote ~tp:p_fib thingy in
        Debug.print "tail %a@.             %a@." D.dump thingy S.dump q;
        q
        end
      in
      let bdy = Hom.run (bdy_tac pos_var neg_var) (q, tail) in
      Debug.print "ran body: %a@." S.dump bdy;
      S.HomLam (S.Lam (pos_name, bdy))
    in ok
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
      Debug.print "building fibs for Hom.elim@.";
      TB.pi (TB.fib q q_base) @@ fun _ -> TB.fib p p_base
    in
    tp, S.HomElim (hom, p_base)
  | _ ->
    Error.error `TypeError "Tried to eliminate from non-hom."

let pos_let ?(name = `Anon) (tm : Syn.tac) (f : Var.tac -> Hom.tac) =
  Hom.rule @@ fun r ->
  let tp, tm = Syn.run tm in
  let v = Eff.eval tm in
  Var.concrete ~name tp v @@ fun v ->
  let steps = Hom.run (f v) r in
  S.Let (name, tm, steps)

let neg_let ?(name = `Anon) (tm : NegSyn.tac) (f : NegVar.tac -> Hom.tac) =
  Hom.rule @@ fun r ->
  let tp, tm = NegSyn.run tm in
  NegVar.abstract ~name tp @@ fun v ->
  Debug.print "reading from %a = %a@." Ident.pp name D.dump (NegVar.borrow v);
  tm (NegVar.borrow v);
  Debug.print "-> read from %a = %a@." Ident.pp name D.dump (NegVar.borrow v);
  Hom.run (f v) r

let neg_ap (neg_tac : NegChk.tac) (fn_tac : Syn.tac) =
  NegSyn.rule @@ fun () ->
  Debug.print "Doing a neg ap@.";
  let fn_tp, fn = Syn.run fn_tac in
  let f = (eval fn) in
  match fn_tp with
  | D.Pi (_, a, clo) ->
    begin
      match inst_const_clo ~tp:a clo with
      | Some b ->
        let neg = NegChk.run neg_tac b in
        Debug.print "b in neg_ap: %a@." S.dump (quote ~tp:D.Univ b);
        Debug.print "%a in neg_ap@." S.dump (quote ~tp:D.Univ a);
        a, fun v -> neg (do_ap f v)
      | None ->
        Error.error `TypeError "The skolem. He escaped his scope. Yes. YES. The skolem is out."
    end
  | _ ->
    Error.error `TypeError "Must do a neg ap against a function."

let drop : NegChk.tac =
  NegChk.rule @@ fun _ ->
  fun _ -> ()

let set (pos_tac : Syn.tac) (neg_tac : NegChk.tac) (steps_tac : Hom.tac) : Hom.tac =
  Hom.rule @@ fun q ->
  let pos_tp, pos = Syn.run pos_tac in
  let neg = NegChk.run neg_tac pos_tp in
  neg (eval pos);
  Hom.run steps_tac q

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
    let phi_v = do_hom_elim (eval phi) vpos in
    let phi_base = do_fst phi_v in
    let phi_fib = do_snd phi_v in
    Var.concrete ~name:pos_name (do_base q) phi_base @@ fun pos_var ->
    NegVar.abstract ~name:neg_name (do_fib q (Var.value pos_var)) @@ fun neg_var ->
    neg (do_ap phi_fib (NegVar.borrow neg_var));
    let steps = Hom.run (steps_tac pos_var neg_var) r in
    S.Let (pos_name, S.Fst (S.HomElim (phi, pos)), steps)
  | _ ->
    Error.error `TypeError "Must ap a hom to a hom!"

(* done is a reserved keyword :) *)
let done_ (pos_tac : Chk.tac) (neg_tac : NegChk.tac) : Hom.tac =
  Hom.rule @@ fun (r, i) ->
  let pos = Chk.run pos_tac (do_base r) in
  let fib = (do_fib r (eval pos)) in
  let name = `Machine (Eff.Locals.size ()) in
  Eff.Locals.abstract ~name fib @@ fun v ->
    let neg = NegChk.run neg_tac fib in
    neg v;
    let fib_act = i () in
    match Eff.Locals.all_consumed () with
    | true ->
      ((Eff.Locals.ppenv ()).pos |>
        Bwd.Bwd.iter @@ fun v ->
          Debug.print "  - %a@." Ident.pp v);
      Debug.print " ---- @.";
      ((Eff.Locals.qenv ()).neg |>
        Bwd.Bwd.iter @@ fun v ->
          Debug.print "  - %a@." D.dump v);
      Debug.print " ---- @.";
      (Bwd.Bwd.iter2
        (fun tp v ->
          Debug.print "  - %a@." S.dump (quote ~tp v))
        (Eff.Locals.qenv ()).neg
        (Eff.Locals.denv ()).neg
      );
      Debug.print " ---- @.";
      (Bwd.Bwd.iter2
        (fun tp v ->
          Debug.print "  - %a@." (S.pp (Eff.Locals.ppenv ()) S.P.isolated) (quote ~tp v))
        (Eff.Locals.denv ()).neg
        (Eff.Locals.qenv ()).neg
      );
      Debug.print " ---- @.";
      Debug.print "%a@." S.dump fib_act;
      S.Pair (pos, S.Lam (name, fib_act))
    | false ->
      Error.error `LinearVariablesNotUsed "Didn't use all your linear variables."
