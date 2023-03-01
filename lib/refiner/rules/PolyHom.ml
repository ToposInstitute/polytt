open Tactic

let formation p_tac q_tac =
  Chk.rule @@
  function
  | D.Univ ->
    let p = Chk.run p_tac D.Poly in
    let q = Chk.run q_tac D.Poly in
    S.PolyHom (p, q)
  | _ ->
    Error.error `TypeError "Poly hom must be in type."

let intro fwd_tac bwd_tac =
  Chk.rule @@
  function
  | D.PolyHom (p, q) ->
    let fwd_tp =
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.build @@
      TB.pi (TB.base p) @@ fun _ -> TB.base q
    in
    let fwd = Chk.run fwd_tac fwd_tp in
    let vfwd = eval fwd in
    let bwd_tp =
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value q @@ fun q ->
      Graft.value vfwd @@ fun fwd ->
      Graft.build @@
      TB.pi (TB.base p) @@ fun base_p ->
      TB.pi (TB.fib q (TB.ap fwd base_p)) @@ fun _ ->
      TB.fib p base_p
    in
    let bwd = Chk.run bwd_tac bwd_tp in
    S.PolyHomIntro (fwd, bwd)
  | _ ->
    Error.error `TypeError "Poly intro must be in poly hom."

let lam ?(name = `Anon) bdy_tac =
  Chk.rule @@
  function
  | D.PolyHom (p, q) ->
    (* FIXME: Linearity! *)
    Var.abstract ~name p @@ fun var_p ->
    let bdy = Chk.run (bdy_tac var_p) q in
    S.PolyHomLam (name, bdy)
  | _ ->
    Error.error `TypeError "Poly lam must be in poly hom."


let base f_tac x_tac =
  Syn.rule @@ fun () ->
  let f_tp, f = Syn.run f_tac in
  match f_tp with
  | D.PolyHom (p, q) ->
    let x = Chk.run x_tac (do_base p) in
    do_base q, S.HomBase (f, x)
  | _ ->
    Error.error `TypeError "Poly base must be applied to a poly hom."

let fib f_tac base_tac fib_tac =
  Syn.rule @@ fun () ->
  let f_tp, f = Syn.run f_tac in
  match f_tp with
  | D.PolyHom (p, q) ->
    let vf = eval f in
    let base = Chk.run base_tac (do_base p) in
    let vbase = eval base in
    let fib_tp =
      graft_value @@
      Graft.value q @@ fun q ->
      Graft.value vf @@ fun f ->
      Graft.value vbase @@ fun base ->
      Graft.build @@
      TB.fib q (TB.hom_base f base)
    in
    let fib = Chk.run fib_tac fib_tp in
    let tp =
      graft_value @@
      Graft.value p @@ fun p ->
      Graft.value vbase @@ fun base ->
      Graft.build @@
      TB.fib p base
    in
    tp, S.HomFib (f, base, fib)
  | _ ->
    Error.error `TypeError "Poly fib must be applied to a poly hom."
