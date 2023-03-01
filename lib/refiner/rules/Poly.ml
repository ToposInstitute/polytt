open Tactic

let formation =
  Chk.rule @@
  function
  | D.Univ ->
    S.Poly
  | _ ->
    Error.error `TypeError "Poly must be in type."

let intro base_tac fib_tac =
  Chk.rule @@
  function
  | D.Poly ->
    let base = Chk.run base_tac D.Univ in
    let vbase = eval base in
    let fib_tp =
      graft_value @@
      Graft.value vbase @@ fun base ->
      Graft.build @@
      TB.pi base @@ fun _ -> TB.univ
    in
    let fib = Chk.run fib_tac fib_tp in
    S.PolyIntro (base, fib)
  | _ ->
    Error.error `TypeError "poly-intro must be in poly."

let base p_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  D.Univ, S.Base p

let fib p_tac x_tac =
  Syn.rule @@ fun () ->
  let p = Chk.run p_tac D.Poly in
  let vp = eval p in
  let x = Chk.run x_tac (do_base vp) in
  D.Univ, S.Fib (p, x)
