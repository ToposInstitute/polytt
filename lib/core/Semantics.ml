open Bwd
open Bwd.Infix

module S = Syntax
module D = Domain

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
    | S.Univ ->
      D.Univ

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_, clo) ->
      inst_clo clo arg
    | D.Neu (Pi(_, a, clo), neu) ->
      let fib = inst_clo clo arg in
      D.Neu (fib, D.push_frm neu (D.Ap { tp = a; arg }))
    | _ ->
      invalid_arg "bad do_ap"

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

let inst_clo =
  Internal.inst_clo

let graft_value =
  Internal.graft_value
