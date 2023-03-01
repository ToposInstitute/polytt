open Tactic
open Eff
open Errors

let formation ?(name = `Anon) base_tac fam_tac =
  Syn.rule @@ fun () ->
    let base = Chk.run base_tac D.Univ in
    let fam = Var.abstract ~name (eval base) @@ fun a ->
      Chk.run (fam_tac a) D.Univ
    in
    (D.Univ, S.Pi(name, base, fam))

let intro ?(name = `Anon) tac =
  Chk.rule @@ function
  | D.Pi (_, a, clo) ->
    Var.abstract ~name a @@ fun v ->
    let fib = inst_clo clo (Var.value v) in
    S.Lam (name, Chk.run (tac v) fib)
  | _ ->
    Error.error `TypeError "Expected element of Π."

let ap f_tac arg_tac =
  Syn.rule @@ fun () ->
  let (f_tp, f) = Syn.run f_tac in
  match f_tp with
  | D.Pi (_, a, clo) ->
    let arg = Chk.run arg_tac a in
    let fib = inst_clo clo (eval arg) in
    fib, S.Ap(f, arg)
  | _ ->
    Error.error `TypeError "Expected element of Π."
