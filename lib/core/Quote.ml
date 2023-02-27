open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics

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
    | _, D.Univ ->
      S.Univ
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
end

let quote ~size ~tp v =
  Internal.Eff.run ~env:size @@ fun () ->
  Internal.quote tp v
