open Bwd
open Bwd.Infix

module S = Syntax
module D = Domain

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

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_, clo) ->
      inst_clo clo arg
    | D.Neu (Pi(_, _, clo), neu) ->
      let fib = inst_clo clo arg in
      D.Neu (fib, D.push_frm neu (D.Ap { tp = fib; arg }))
    | _ ->
      invalid_arg "bad do_ap"

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Eff.run ~env:(env #< v) (fun () -> eval body)
end
