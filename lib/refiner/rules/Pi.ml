open Tactic
open Eff
open Core.Ident

let formation ?(names = [Var `Anon]) base_tac fam_tac =
  Syn.rule @@ fun () ->
  let base = Chk.run base_tac D.Univ in
  let fam = Var.abstracts ~names (eval base) @@ fun xs ->
    Chk.run (fam_tac xs) D.Univ
  in
  (D.Univ, List.fold_right (fun name tp -> S.Pi (name, base, tp)) (Var.choose_many names) fam)

let rec intro ?(name = Var `Anon) tac =
  Chk.rule @@ function
  | D.Pi (_, a, clo) ->
    Var.abstract ~name a @@ fun v ->
    let fib = inst_clo clo (Var.value v) in
    S.Lam (Var.choose name, Chk.run (tac v) fib)
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

let intro_syn ?(names = [Var `Anon]) tp_tac tac =
  Syn.rule @@ fun () ->
  let stp = Chk.run tp_tac D.Univ in
  let tp = eval stp in
  let (rtp, r) = Var.abstracts ~names tp @@ fun v -> Syn.run (tac v) in
  let fntp = graft_value @@
    Graft.value tp @@ fun tp ->
    Graft.value rtp @@ fun rtp ->
    Graft.build @@
    List.fold_right (fun name rtp -> TB.pi ~name tp @@ fun _ -> rtp) (Var.choose_many names) rtp
  in
  (fntp, List.fold_right (fun name r -> S.Lam (name, r)) (Var.choose_many names) r)

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
