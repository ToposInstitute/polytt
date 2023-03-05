open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics

open TermBuilder

module Internal =
struct
  module Eff = Algaeff.Reader.Make (struct type env = int end)

  let bind tp f =
    let arg = D.var tp @@ Eff.read() in
    Eff.scope (fun size -> size + 1) @@ fun () ->
    f arg

  let quote_lvl lvl =
    let env = Eff.read () in
    env - (lvl + 1)

  let rec quote (tp : D.t) (v : D.t) : S.t =
    match tp, v with
    (* | D.Pi (_nm, D.FinSet ls, tp_clo), D.Lam (nm, clo) when ls != [] ->
      (* Debug.print "Lam-FinSet ETA@."; *)
      S.Lam (nm,
        S.Cases
          ( S.Lam (_nm, bind (D.FinSet ls) @@ fun arg -> quote D.Univ (Sem.inst_clo tp_clo arg))
          , List.map (fun l ->
                let arg = D.Label (ls, l) in
                l, quote (Sem.inst_clo tp_clo arg) (Sem.inst_clo clo arg)
            ) ls
          , S.Var 0
          )
      ) *)
    | D.Pi (_, a, tp_clo), D.Lam (nm, clo) ->
      let body = bind a @@ fun arg ->
        quote (Sem.inst_clo tp_clo arg) (Sem.inst_clo clo arg)
      in
      S.Lam (nm, body)
    | D.Pi (nm, a, clo), v ->
      let body = bind a @@ fun arg ->
        quote (Sem.inst_clo clo arg) @@ Sem.do_ap v arg
      in
      S.Lam(nm, body)
    (* | _, D.Pi (nm, D.FinSet ls, clo) when ls != [] ->
      (* Debug.print "Pi-FinSet ETA@."; *)
      S.Pi (nm, S.FinSet ls,
        S.Cases
          ( S.Lam (nm, S.Univ)
          , List.map (fun l ->
                let arg = D.Label (ls, l) in
                l, quote D.Univ (Sem.inst_clo clo arg)
            ) ls
          , S.Var 0
          )
      ) *)
    | _, D.Pi (nm, a, clo) ->
      let qa = quote D.Univ a in
      let b = bind a @@ fun arg ->
        quote D.Univ (Sem.inst_clo clo arg)
      in
      S.Pi (nm, qa, b)
    | _, D.Sigma (nm, a, clo) ->
      let qa = quote D.Univ a in
      let b = bind a @@ fun arg ->
        quote D.Univ (Sem.inst_clo clo arg)
      in
      S.Sigma (nm, qa, b)
    | D.Sigma (_, a, tp_clo), D.Pair (v1, v2) ->
      let t1 = quote a v1 in
      let t2 = quote (Sem.inst_clo tp_clo v1) v2 in
      S.Pair (t1, t2)
    | D.Sigma (_, a, tp_clo), v ->
      let v1 = Sem.do_fst v in
      let t1 = quote a v1 in
      let t2 = quote (Sem.inst_clo tp_clo v1) (Sem.do_snd v) in
      S.Pair (t1, t2)
    | _, D.Eq (tp, tm1, tm2) ->
      S.Eq (quote D.Univ tp, quote tp tm1, quote tp tm2)
    | D.Eq (tp, _, _), D.Refl tm ->
      S.Refl (quote tp tm)
    | _, D.Nat ->
      S.Nat
    | _, D.Zero ->
      S.Zero
    | _, D.Succ n ->
      S.Succ (quote D.Nat n)
    | _, D.Univ ->
      S.Univ
    | _, D.NegUniv ->
      S.NegUniv
    | _, D.NegSigma (name, a, b) ->
      let qa = quote D.Univ a in
      let b = bind a @@ fun arg ->
        quote D.NegUniv (Sem.inst_clo b arg)
      in
      S.NegSigma (name, qa, b)
    | _, D.Poly ->
      S.Poly
    | D.Poly, D.PolyIntro (vbase, vfib) ->
      let base = quote D.Univ vbase in
      let fib = bind vbase @@ fun arg ->
        quote D.Univ (Sem.inst_clo vfib arg)
      in
      S.PolyIntro (base, fib)
    | D.Poly, v ->
      let base = Sem.do_base v in
      let qbase = quote D.Univ base in
      let fib = bind base @@ fun i ->
        quote D.Univ (Sem.do_fib v i)
      in S.PolyIntro (qbase, fib)
    | _, D.Hom (p, q) ->
      S.Hom (quote D.Poly p, quote D.Poly q)
    | D.Hom (p, q), D.HomLam (pos_name, neg_name, clo) ->
      bind (Sem.do_base p) @@ fun p_base ->
      let v = Sem.inst_hom_clo clo p_base in
      let q_base = Sem.do_fst v in
      let qq_base = quote (Sem.do_base q) q_base in
      let qp_fib =
        bind (Sem.do_fib q q_base) @@ fun q_fib ->
        quote (Sem.do_fib p p_base) (Sem.do_ap (Sem.do_snd v) q_fib)
      in
      (* let prog = S.Lam (p_name, S.Pair(qq_base, S.Lam (q_name, qp_fib))) in *)
      S.HomLam (pos_name, neg_name, S.Done (qq_base, S.NegAp (S.Var 0, S.Lam(`Anon, qp_fib))))
    | _, D.FinSet ls ->
      S.FinSet ls
    | _, D.Label (ls, l) ->
      S.Label (ls, l)
    | _, D.Neu (_, neu) ->
      quote_neu neu
    | tp, tm ->
      Debug.print "Bad quote: %a@." D.dump tm;
      invalid_arg "bad quote"

  and quote_neu {hd; spine} =
    Bwd.fold_left quote_frm (quote_hd hd) spine

  and quote_hd hd =
    match hd with
    | D.Var lvl ->
      S.Var (quote_lvl lvl)
    | D.Hole (tp, n) ->
      S.Hole (quote D.Univ tp, n)
    | D.Skolem tp ->
      S.Skolem (quote D.Univ tp)
    | D.Negate tp ->
      S.Negate (quote D.Univ tp)

  and quote_frm tm frm =
    match frm with
    | D.Ap {tp; arg} ->
      S.Ap (tm, quote tp arg)
    | D.Fst ->
      S.Fst tm
    | D.Snd ->
      S.Snd tm
    | D.NatElim {mot; zero; succ} ->
      let mot_tp =
        Sem.graft_value @@
        Graft.build @@
        TB.pi TB.nat @@ fun _ -> TB.univ
      in
      let qmot = quote mot_tp mot in
      let qzero = quote (Sem.do_ap mot D.Zero) zero in
      let succ_tp =
        Sem.graft_value @@
        Graft.value mot @@ fun mot ->
        Graft.build @@
        TB.pi TB.nat @@ fun n ->
        TB.pi (TB.ap mot n) @@ fun _ ->
        TB.ap mot (TB.succ n)
      in
      let qsucc = quote succ_tp succ in
      S.NatElim { mot = qmot; zero = qzero; succ = qsucc; scrut = tm }
    | D.Cases {mot; cases} ->
      let ls = List.map fst cases in
      let quote_key (l, v) = l, quote (Sem.do_ap mot (D.Label (ls, l))) v in
      S.Cases (quote (Sem.graft_value (Graft.build (TB.pi (TB.finset ls) (fun _ -> TB.univ)))) mot, List.map quote_key cases, tm)
    | D.Base ->
      S.Base tm
    | D.Fib {base; value} ->
      S.Fib (tm, quote base value)
    | D.HomElim {tp; value} ->
      S.HomElim (tm, quote tp value)
    | D.UnNegate ->
      S.UnNegate tm
end

let quote ~size ~tp v =
  Internal.Eff.run ~env:size @@ fun () ->
  Internal.quote tp v

let quote_top ~tp v =
  Internal.Eff.run ~env:0 @@ fun () ->
  Internal.quote tp v
