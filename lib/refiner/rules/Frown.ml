open Tactic

let formation p_tac q_tac f_tac =
  Chk.rule @@
  function
  | D.Poly ->
    let p = Chk.run p_tac D.Poly in
    let q = Chk.run q_tac D.Poly in
    let vp = eval p in
    let vq = eval q in
    let f_tp =
      graft_value @@
      Graft.value vp @@ fun p ->
      Graft.value vq @@ fun q ->
      Graft.build @@
      TB.pi (TB.base p) @@ fun _ -> TB.base q
    in
    let f = Chk.run f_tac f_tp in
    S.Frown (p, q, f)
  | _ ->
    Error.error `TypeError "Tensor must be in Poly."

