open Tactic
open Core.Ident

let formation =
  Chk.rule @@
  function
  | D.Univ ->
    S.Poly
  | _ ->
    Error.error `TypeError "Poly must be in type."

let repr_formation =
  Chk.rule @@
  function
  | D.Univ ->
    S.Repr
  | _ ->
    Error.error `TypeError "Repr must be in type."

let intro ?(name = Var `Anon) base_tac fib_tac =
  Chk.rule @@
  function
  | D.Poly ->
    let base = Chk.run base_tac D.Univ in
    let vbase = eval base in
    let fib =
      Var.abstract ~name vbase @@ fun var ->
      Chk.run (fib_tac var) D.Univ
    in
    S.PolyIntro (Var.choose name, base, fib)
  | _ ->
    Error.error `TypeError "Poly intro must be in poly."

let repr_intro exp_tac =
  Chk.rule @@
  function
  | D.Poly ->
    let exp = Var.abstract (D.FinSet ["unit"]) @@ fun _ -> Chk.run exp_tac D.Univ in
    S.PolyIntro (`Anon, S.FinSet ["unit"], exp)
  | D.Repr ->
    let exp = Chk.run exp_tac D.Univ in
    S.ReprIntro exp
  | _ ->
    Error.error `TypeError "Poly intro must be in poly."

let base p_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  D.Univ, S.Base p

let fib p_tac i_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  let vp = eval p in
  let i = Chk.run i_tac (do_base vp) in
  D.Univ, S.Fib (p, i)

let log r_tac =
  Syn.rule @@ fun () ->
  let r = Chk.run r_tac D.Repr in
  D.Univ, S.Log r
