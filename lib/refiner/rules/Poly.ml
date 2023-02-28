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
  let (p_tp, p) = Syn.run p_tac in
  match p_tp with
  | D.Poly ->
    D.Univ, S.Base p
  | _ ->
    Error.error `TypeError "base must eliminate out of a poly."

let fib p_tac x_tac =
  Syn.rule @@ fun () ->
  let (p_tp, p) = Syn.run p_tac in
  match p_tp with
  | D.Poly ->
    let vp = eval p in
    let x = Chk.run x_tac (do_base vp) in
    D.Univ, S.Fib (p, x)
  | _ ->
    Error.error `TypeError "base must eliminate out of a poly."
