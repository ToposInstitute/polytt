open Bwd
open Bwd.Infix

module S = Syntax
module D = Domain
module MS = Map.Make(String)

open TermBuilder

module Internal =
struct
  type env = D.env
  module Eff = Algaeff.Reader.Make (struct type nonrec env = env end)

  let var ix =
    let env = Eff.read () in
    Bwd.nth env ix

  let clo body =
    let env = Eff.read () in
    D.Clo { env; body }

  let append vals k =
    Eff.scope (fun env -> Bwd.append env vals) k

  let rec eval (tm : S.t) : D.t =
    match tm with
    | S.Var ix ->
      var ix
    | S.Pi (nm, a, b) ->
      D.Pi (nm, eval a, clo b)
    | S.Lam (nm, b) ->
      D.Lam (nm, clo b)
    | S.Ap (f, a) ->
      do_ap (eval f) (eval a)
    | S.Sigma (nm, a, b) ->
      D.Sigma (nm, eval a, clo b)
    | S.Pair (a, b) ->
      D.Pair (eval a, eval b)
    | S.Fst tm ->
      do_fst (eval tm)
    | S.Snd tm ->
      do_snd (eval tm)
    | S.Nat ->
      D.Nat
    | S.Zero ->
      D.Zero
    | S.Succ n ->
      D.Succ (eval n)
    | S.NatElim {mot; zero; succ; scrut} ->
      do_nat_elim (eval mot) (eval zero) (eval succ) (eval scrut)
    | S.FinSet ls ->
      D.FinSet ls
    | S.Label (ls, l) ->
      D.Label (ls, l)
    | S.Cases (mot, cases, case) ->
      do_cases (eval mot) (List.map (fun (l, v) -> l, eval v) cases) (eval case)
    | S.Univ ->
      D.Univ
    | S.Poly ->
      D.Poly
    | S.PolyIntro (b, fib) ->
      D.PolyIntro (eval b, eval fib)
    | S.Base p ->
      do_base (eval p)
    | S.Fib (p, x) ->
      do_fib (eval p) (eval x)
    | S.PolyHom (p, q) ->
      D.PolyHom (eval p, eval q)
    | S.PolyHomIntro (fwd, bwd) ->
      D.PolyHomIntro (eval fwd, eval bwd)
    | S.PolyHomLam (nm, tm) ->
      D.PolyHomLam (nm, clo tm)
    | S.HomBase (f, x) ->
      do_hom_base (eval f) (eval x)
    | S.HomFib (f, x, qx) ->
      do_hom_fib (eval f) (eval x) (eval qx)
    | S.Tensor (p, q) ->
      D.Tensor (eval p, eval q)
    | S.TensorIntro (p, q) ->
      D.TensorIntro (eval p, eval q)
    | S.TensorElim (mot, bdy, scrut) ->
      do_tensor_elim (eval mot) (clo bdy) (eval scrut)
    | S.Tri (p, q) ->
      D.Tri (eval p, eval q)
    | S.TriIntro (f, r) ->
      failwith "FIXME: tri-intro"
    | S.Frown (p, q, f) ->
      D.Frown (eval p, eval q, eval f)

  (** Evaluate the body of a poly lambda 'P ⇒ Q' as a map 'base P → base Q'.
      The 'base P' value is bound as the final element of the context.

      As this is the "forward mode" of poly hom evaluation, the general pattern
      is to take introduction forms to introduction forms, and elimination forms
      to elimination forms. *)
  and eval_hom_base f =
    match f with
    | S.Var ix ->
      var ix
    | S.TensorIntro (p, q) ->
      D.Pair (eval_hom_base p, eval_hom_base q)
    | S.TensorElim (_, bdy, scrut) ->
      let scrut = eval_hom_base scrut in
      (* Tensor is a positive type, whereas sigma is negative, which leads to this oddity. *)
      append [do_fst scrut; do_snd scrut] @@ fun () ->
      eval_hom_base bdy
    | _ ->
      invalid_arg "bad do_eval_hom_base"

  (** Evaluate the body of a poly lambda 'f : P ⇒ Q' as a map
      '(x : base P) → fib Q (hom-base f x) → base Q'.
      We bind the 'base P' and 'fib Q (hom-base f x)' variables
      as a /pair/ in the environment. This makes it easier to handle
      the calling other poly-homs that come from the ambient environment,
      and also clarifies the variable rule.

      As this is the "backward mode" of poly hom evaluation, the general pattern
      is to take introduction forms to /elimination/ forms, and elimination forms
      to introduction forms.


      > def swap : (P : poly) → (Q : poly) → (P ⊗ Q ⇒ Q ⊗ P) :=
      >  λ P Q → λ pq → ⊗-elim (Q ⊗ P) (λ p q → (q , p)) pq
  *)
  and dispatch_eval_hom_fib vars f fib =
    match f with
    | S.Var ix ->
      Debug.print "Writing to cell %d@." ix;
      CCVector.set vars (CCVector.length vars - ix - 1) (Some fib);
      var ix
    | S.TensorIntro (p, q) ->
      let p_base = dispatch_eval_hom_fib vars p (do_fst fib) in
      let q_base = dispatch_eval_hom_fib vars q (do_snd fib) in
      D.Pair (p_base, q_base)
    | S.TensorElim (_, bdy, scrut) ->
      (* Annoying time/space trade-off. To be able to compute the reverse direction
         of the body of a tensor elim, we need to know the base value of scrut to
         be able to bind vars in the environment. This does lead to a bit of duplicate
         computation when we compute the fibre of scrut. *)
      let scrut_base = eval_hom_base scrut in
      CCVector.push vars None;
      CCVector.push vars None;
      Debug.print "Pushed cells, have %d cells now.@." (CCVector.length vars);
      let bdy_base = append [do_fst scrut_base; do_snd scrut_base] @@ fun () ->
        dispatch_eval_hom_fib vars bdy fib
      in
      let q_fib = Option.get @@ CCVector.pop_exn vars in
      let p_fib = Option.get @@ CCVector.pop_exn vars in
      Debug.print "Popped cells, have %d cells now.@." (CCVector.length vars);
      (* We've already computed scrut_base, so we discard it. *)
      let _ = dispatch_eval_hom_fib vars scrut (D.Pair (p_fib, q_fib)) in
      bdy_base
    | _ ->
      invalid_arg "bad do_eval_hom_fib"

  and eval_hom_fib f fib =
    let vars = CCVector.make 1 None in
    let _ = dispatch_eval_hom_fib vars f fib in
    Option.get @@ CCVector.pop_exn vars

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_t, clo) ->
      inst_clo clo arg
    | D.Neu (Pi(_t, a, clo), neu) ->
      let fib = inst_clo clo arg in
      D.Neu (fib, D.push_frm neu (D.Ap { tp = a; arg }))
    | _ ->
      invalid_arg "bad do_ap"

  and do_aps f args =
    List.fold_left do_ap f args

  and do_fst (v: D.t) =
    match v with
    | D.Pair (a, _b) ->
      a
    | D.Neu (D.Sigma (_, a, _clo), neu) ->
      D.Neu (a, D.push_frm neu D.Fst)
    | _ ->
      invalid_arg "bad do_fst"

  and do_snd (v: D.t) =
    match v with
    | D.Pair (_a, b) ->
      b
    | D.Neu (D.Sigma (_, _a, clo), neu) ->
      let fib = inst_clo clo (do_fst v) in
      D.Neu (fib, D.push_frm neu D.Snd)
    | _ ->
      invalid_arg "bad do_snd"

  and do_cases mot cases case =
    match case with
    | D.Label (_, l) ->
      MS.find l (MS.of_seq (List.to_seq cases))
    | D.Neu (D.FinSet _, neu) as n ->
      let fib = do_ap mot n in
      D.Neu (fib, D.push_frm neu (D.Cases { mot; cases }))
    | _ ->
      invalid_arg "bad do_cases"

  and do_nat_elim mot zero succ scrut =
    let rec rec_nat_elim =
      function
      | D.Zero ->
        zero
      | D.Succ n ->
        do_aps succ [n; rec_nat_elim n]
      | D.Neu (_, neu) as n ->
        let fib = do_ap mot n in
        D.Neu (fib, D.push_frm neu (D.NatElim { mot; zero; succ }))
      | _ ->
        invalid_arg "bad do_nat_elim"
    in rec_nat_elim scrut

  and do_base p =
    match p with
    | D.PolyIntro (b, _) ->
      b
    | D.Tensor (p, q) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.build @@
      TB.sigma (TB.base p) @@ fun _ -> (TB.base q)
    | D.Tri (p, q) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.build @@
      TB.sigma (TB.base p) @@ fun basex ->
      TB.pi (TB.fib p basex) @@ fun _ ->
      TB.base q
    | D.Frown (p, q, f) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.value f @@ fun f ->
      Graft.build @@
      TB.sigma (TB.base p) @@ fun basex ->
      TB.fib q (TB.ap f basex)
    | D.Neu (_, neu) ->
      D.Neu (D.Univ, D.push_frm neu D.Base)
    | _ ->
      invalid_arg "bad do_base"

  and do_fib p x =
    match p with
    | D.PolyIntro (_, fib) ->
      do_ap fib x
    | D.Tensor (p, q) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.value x @@ fun x ->
      Graft.build @@
      TB.sigma (TB.fib p x) @@ fun _ -> (TB.fib q x)
    | D.Tri (p, q) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.value x @@ fun x ->
      Graft.build @@
      TB.sigma (TB.fib p @@ TB.fst x) @@ fun fibx ->
      TB.fib q (TB.ap (TB.snd x) fibx)
    | D.Frown (p, _q, _f) ->
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value x @@ fun x ->
      Graft.build @@
      TB.fib p (TB.fst x)
    | D.Neu (_, neu) ->
      D.Neu (D.Univ, D.push_frm neu (D.Fib { tp = do_base p; base = x }))
    | _ ->
      invalid_arg "bad do_fib"

  and do_hom_base f x =
    match f with
    | D.PolyHomIntro (fwd, _) ->
      do_ap fwd x
    | D.PolyHomLam (_, clo) ->
      inst_hom_clo_base clo x
    | D.Neu (D.PolyHom (p, q), neu) ->
      let q_base = do_base q in
      D.Neu (q_base, D.push_frm neu (D.HomBase { p; base = x }))
    | _ ->
      invalid_arg "bad do_hom_base"

  and do_hom_fib f x qx =
    match f with
    | D.PolyHomIntro (_, bwd) ->
      do_aps bwd [x; qx]
    | D.PolyHomLam (_, clo) ->
      inst_hom_clo_fib clo x qx
    | D.Neu (D.PolyHom (p, q), neu) ->
      let q_base = do_base q in
      D.Neu (q_base, D.push_frm neu (D.HomFib { p; base = x; fib = qx }))
    | _ ->
      invalid_arg "bad do_hom_base"

  and do_tensor_elim mot bdy scrut =
    match scrut with
    | D.TensorIntro (p, q) ->
      inst_clo2 bdy p q
    | D.Neu (D.Tensor (p, q), neu) ->
      D.Neu (mot, D.push_frm neu (D.TensorElim {p; q; mot; bdy}))
    | _ ->
      invalid_arg "bad do_tensor_elim"

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< v) (fun () -> eval body)

  and inst_hom_clo_base clo v =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< v) (fun () -> eval_hom_base body)

  and inst_hom_clo_fib clo base fib =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< base) (fun () -> eval_hom_fib body fib)

  and inst_clo2 clo v1 v2 =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< v1 #< v2) (fun () -> eval body)

  and graft_value (gtm : S.t Graft.t) =
    let tm, env = Graft.graft gtm in
    Eff.run ~env @@ fun () -> eval tm
end

let eval ~env tm =
  Internal.Eff.run ~env @@ fun () ->
  Internal.eval tm

let eval_top tm =
  eval ~env:Emp tm

let do_ap =
  Internal.do_ap

let do_fst =
  Internal.do_fst

let do_snd =
  Internal.do_snd

let do_nat_elim ~mot ~zero ~succ ~scrut =
  Internal.do_nat_elim mot zero succ scrut

let do_base p =
  Internal.do_base p

let do_fib p x =
  Internal.do_fib p x

let inst_clo =
  Internal.inst_clo

let inst_clo2 =
  Internal.inst_clo2

let graft_value =
  Internal.graft_value
