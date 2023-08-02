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
    let pr, isPoly =
      Var.abstract ~name vbase @@ fun var ->
        Chk.run2 (fib_tac var) D.Repr D.Poly
    in if isPoly
      then
        S.Ap
          ( S.Ap
              ( S.Lam
                  ( Var.fresh_name `Anon
                  , S.Lam
                      ( Var.fresh_name `Anon
                      , S.PolyIntro
                        ( Var.fresh_name `Anon
                        , S.Sigma (Var.choose name, S.Var 1, S.Base (S.Ap (S.Var 1, S.Var 0)))
                        , S.Fib (S.Ap (S.Var 1, S.Fst (S.Var 0)), S.Snd (S.Var 0))
                        )
                      )
                  )
              , base
              )
          , S.Lam (Var.choose name, pr)
          )
      else S.PolyIntro (Var.choose name, base, S.Log pr)
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
