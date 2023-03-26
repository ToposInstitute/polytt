open Tactic

let formation =
  Chk.rule @@
  function
  | D.Univ ->
    S.Poly
  | _ ->
    Error.error `TypeError "Poly must be in type."

let intro ?(name = `Anon) base_tac fib_tac =
  Chk.rule @@
  function
  | D.Poly ->
    let base = Chk.run base_tac D.Univ in
    let vbase = eval base in
    let fib =
      Var.abstract ~name vbase @@ fun var ->
      Chk.run (fib_tac var) D.Univ
    in
    S.PolyIntro (name, base, fib)
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
