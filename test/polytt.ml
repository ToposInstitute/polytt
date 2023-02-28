open Core

module S = Syntax
open Ident

let abs v = user [v]

let test expected term =
  let result = Format.asprintf "%a" S.pp_toplevel term in
  if result = expected then () else
    let () = Format.printf "%s\n%s\n" result expected in
    failwith "Not what was expected"


let () = test "λ x. λ y. x" (S.Lam (abs "x", S.Lam (abs "y", S.Var 1)))
let () = test "(λ x. x) (λ y. y)" (S.Ap (S.Lam (abs "x", S.Var 0), S.Lam (abs "y", S.Var 0)))
let () = test "(λ x. x, λ y. y)" (S.Pair (S.Lam (abs "x", S.Var 0), (S.Lam (abs "y", S.Var 0))))
let () = test "λ x. x x (x x)" (S.Lam (abs "x", S.Ap (S.Ap (S.Var 0, S.Var 0), S.Ap (S.Var 0, S.Var 0))))
(* BlockArguments is an extension :-/ *)
let () = test "λ x. x (λ y. x)" (S.Lam (abs "x", S.Ap (S.Var 0, S.Lam (abs "y", S.Var 1))))
let () = test "λ x. x (fst x x)" (S.Lam (abs "x", S.Ap (S.Var 0, S.Ap (S.Fst (S.Var 0), S.Var 0))))
let () = test "Π(x : U), λ x. x" (S.Pi (abs "x", S.Univ, S.Lam (abs "x", S.Var 0)))
let () = test "Σ(x : λ y. y), x" (S.Sigma (abs "x", S.Lam (abs "y", S.Var 0), S.Var 0))
let () = Format.printf "All good!\n"
