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
    | S.Tensor (p, q) ->
      D.Tensor (eval p, eval q)
    | S.Tri (p, q) ->
      D.Tri (eval p, eval q)
    | S.Frown (p, q, f) ->
      D.Frown (eval p, eval q, eval f)

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

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< v) (fun () -> eval body)

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

let graft_value =
  Internal.graft_value
