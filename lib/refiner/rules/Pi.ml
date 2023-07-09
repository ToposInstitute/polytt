open Tactic
open Eff

let formation ?(names = [`Anon]) base_tac fam_tac =
  Syn.rule @@ fun () ->
  let base = Chk.run base_tac D.Univ in
  let fam = Var.abstracts ~names (eval base) @@ fun xs ->
    Chk.run (fam_tac xs) D.Univ
  in
  (D.Univ, List.fold_right (fun name tp -> S.Pi (name, base, tp)) names fam)

let rec intro ?(name = `Anon) tac =
  Chk.rule @@ function
  | D.Pi (_, a, clo) ->
    Var.abstract ~name a @@ fun v ->
    let fib = inst_clo clo (Var.value v) in
    S.Lam (name, Chk.run (tac v) fib)
  | D.Hom (p, q) ->
    let t = graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.build @@
      TB.pi (TB.base p) @@ fun p_base ->
      TB.sigma (TB.base q) @@ fun q_base ->
      TB.pi (TB.fib q q_base) @@ fun _ -> TB.fib p p_base
    in S.HomLam (Chk.run (intro ~name tac) t)
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
