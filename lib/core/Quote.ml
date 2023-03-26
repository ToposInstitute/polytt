open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics

open TermBuilder

module Env = QuoteEnv

module Internal =
struct
  type env = Env.t
  module Eff = Env.Eff

  let bind tp f =
    let arg = D.var tp (Env.read_pos_size ()) in
    Eff.scope Env.incr_pos @@ fun () ->
    f arg

  let quote_lvl lvl =
    let env = Env.read_pos_size () in
    env - (lvl + 1)

  let rec quote (tp : D.t) (v : D.t) : S.t =
    match tp, v with
    (* | D.Pi (_nm, D.FinSet ls, tp_clo), D.Lam (nm, clo) when ls != [] ->
       Debug.print "Lam-FinSet ETA%a@." D.dump_clo clo;
       let r = S.Lam (nm,
        bind (D.FinSet ls) @@ fun arg ->
        S.Cases
          ( S.Lam (_nm, bind (D.FinSet ls) @@ fun arg -> quote D.Univ (Sem.inst_clo tp_clo arg))
          , List.map (fun l ->
                let arg = D.Label (ls, l) in
                l, quote (Sem.inst_clo tp_clo arg) (Sem.inst_clo clo arg)
            ) ls
          , S.Var 0
          )
       ) in
       Debug.print "ETAD%a@." S.dump r;
       r *)
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
    | _, D.Poly ->
      S.Poly
    | D.Poly, D.PolyIntro (nm, vbase, vfib) ->
      let base = quote D.Univ vbase in
      let fib = bind vbase @@ fun arg ->
        quote D.Univ (Sem.inst_clo vfib arg)
      in
      S.PolyIntro (nm, base, fib)
    | D.Poly, v ->
      let base = Sem.do_base v in
      let qbase = quote D.Univ base in
      let fib = bind base @@ fun i ->
        quote D.Univ (Sem.do_fib v i)
      in S.PolyIntro (`Anon, qbase, fib)
    | _, D.Hom (p, q) ->
      S.Hom (quote D.Poly p, quote D.Poly q)
    | D.Hom (p, q), D.HomLam wrapped ->
      let p_base = Sem.do_base p in
      let tp =
        Sem.graft_value @@
        Graft.value p @@ fun p ->
        Graft.value q @@ fun q ->
        Graft.value p_base @@ fun p_base ->
        Graft.build @@
        TB.sigma (TB.base q) @@ fun q_base ->
        TB.pi (TB.fib q q_base) @@ fun _ -> TB.fib p p_base
      in
      S.HomLam (quote tp wrapped)
    | _, D.FinSet ls ->
      S.FinSet ls
    | _, D.Label (ls, l) ->
      S.Label (ls, l)
    | tp, D.Neu (_, neu) ->
      quote_neu tp neu
    | tp, tm ->
      Debug.print "Bad quote: %a@." D.dump tm;
      Debug.print "  against: %a@." D.dump tp;
      invalid_arg "bad quote"

  and unstick tp hd =
    match hd with
    | D.Borrow lvl ->
      Env.read_neg_lvl lvl
    | _ -> D.Neu (tp, { hd; spine = Emp })

  and quote_neu tp {hd; spine} =
    match unstick tp hd with
    (* still stuck *)
    | D.Neu (_tp, { hd; spine = spine1 }) ->
      Bwd.fold_left quote_frm (Bwd.fold_left quote_frm (quote_hd hd) spine1) spine
    (* made at least a little progress *)
    | e ->
      quote tp (Sem.do_spine e spine)

  and quote_hd hd =
    match hd with
    | D.Var lvl ->
      S.Var (quote_lvl lvl)
    | D.Borrow lvl ->
      S.Borrow lvl
    | D.Hole (tp, n) ->
      S.Hole (quote D.Univ tp, n)
    | D.Skolem tp ->
      S.Skolem (quote D.Univ tp)

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
    | D.HomElim {tp; arg} ->
      S.HomElim (tm, quote tp arg)
end

let quote ~env ~tp v =
  Internal.Eff.run ~env @@ fun () ->
  Internal.quote tp v

let quote_top ~tp v =
  quote ~env:Env.empty ~tp v
