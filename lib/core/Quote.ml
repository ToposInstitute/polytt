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
    | _, D.Pi (nm, a, clo) ->
      let a = quote D.Univ a in
      let b = bind D.Univ @@ fun arg ->
        quote D.Univ (Sem.inst_clo clo arg)
      in
      S.Pi (nm, a, b)
    | _, D.Sigma (nm, a, clo) ->
      let a = quote D.Univ a in
      let b = bind D.Univ @@ fun arg ->
        quote D.Univ (Sem.inst_clo clo arg)
      in
      S.Sigma (nm, a, b)
    | D.Sigma (_, a, tp_clo), D.Pair (v1, v2) ->
      let t1 = quote a v1 in
      let t2 = quote (Sem.inst_clo tp_clo v1) v2 in
      S.Pair (t1, t2)
    | D.Sigma (_, a, tp_clo), v ->
      let v1 = Sem.do_fst v in
      let t1 = quote a v1 in
      let t2 = quote (Sem.inst_clo tp_clo v1) (Sem.do_snd v) in
      S.Pair (t1, t2)
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
    | _, D.PolyIntro (base, fib) ->
      let fib_tp =
        Sem.graft_value @@
        Graft.value base @@ fun base ->
        Graft.build @@
        TB.pi base @@ fun _ -> TB.univ
      in
      S.PolyIntro (quote D.Univ base, quote fib_tp fib)
    | _, D.PolyHom (p, q) ->
      S.PolyHom (quote D.Poly p, quote D.Poly q)
    | D.PolyHom (p, q), D.PolyHomIntro (fwd, bwd) ->
      (* FIXME: η-laws for poly-hom? *)
      let fwd_tp =
        Sem.graft_value @@
        Graft.value p @@ fun p ->
        Graft.value q @@ fun q ->
        Graft.build @@
        TB.pi (TB.base p) @@ fun _ -> TB.base q
      in
      let bwd_tp =
        Sem.graft_value @@
        Graft.value p @@ fun p ->
        Graft.value q @@ fun q ->
        Graft.value fwd @@ fun fwd ->
        Graft.build @@
        TB.pi (TB.base p) @@ fun base_p ->
        TB.pi (TB.fib q (TB.ap fwd base_p)) @@ fun _ ->
        TB.fib p base_p
      in
      S.PolyHomIntro (quote fwd_tp fwd, quote bwd_tp bwd)
    | D.PolyHom (p, q), D.PolyHomLam (name, bdy) ->
      (* FIXME: η-laws for poly-hom? *)
      bind p @@ fun var_p ->
      S.PolyHomLam (name, quote q (Sem.inst_clo bdy var_p))
    | _, D.Tensor (p, q) ->
      S.Tensor (quote D.Poly p, quote D.Poly q)
    | D.Tensor (p, q), D.TensorIntro (px, qx) ->
      S.TensorIntro (quote p px, quote q qx)
    | _, D.Tri (p, q) ->
      S.Tri (quote D.Poly p, quote D.Poly q)
    | _, D.Frown (p, q, f) ->
      let f_tp =
        Sem.graft_value @@
        Graft.value p @@ fun p ->
        Graft.value q @@ fun q ->
        Graft.build @@
        TB.pi (TB.base p) @@ fun _ -> TB.base q
      in
      S.Frown (quote D.Poly p, quote D.Poly q, quote f_tp f)
    | _, D.FinSet ls ->
      S.FinSet ls
    | _, D.Label (ls, l) ->
      S.Label (ls, l)
    | _, D.Neu (_, neu) ->
      quote_neu neu
    | _ ->
      invalid_arg "bad quote"

  and quote_neu {hd; spine} =
    Bwd.fold_left quote_frm (quote_hd hd) spine

  and quote_hd hd =
    match hd with
    | D.Var lvl ->
      S.Var (quote_lvl lvl)

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
    | D.Base ->
      S.Base tm
    | D.Fib {tp; base} ->
      S.Fib (tm, quote tp base)
    | D.HomBase {p; base} ->
      S.HomBase (tm, quote (Sem.do_base p) base)
    | D.TensorElim {p; q; mot; bdy} ->
      bind p @@ fun var_p ->
      bind q @@ fun var_q ->
      let bdy = quote (D.Tensor (p, q)) (Sem.inst_clo2 bdy var_p var_q) in
      S.TensorElim (quote D.Poly mot, bdy, tm)
    | D.Cases {mot; cases} ->
      let ls = List.map fst cases in
      let quote_key (l, v) = l, quote (Sem.do_ap mot (D.Label (ls, l))) v in
      S.Cases (quote (Sem.graft_value (Graft.build (TB.pi (TB.finset ls) (fun _ -> TB.univ)))) mot, List.map quote_key cases, tm)
end

let quote ~size ~tp v =
  Internal.Eff.run ~env:size @@ fun () ->
  Internal.quote tp v

let quote_top ~tp v =
  Internal.Eff.run ~env:0 @@ fun () ->
  Internal.quote tp v
