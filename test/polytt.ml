open Core

module S = Syntax
open Ident

let abs v = user [v]

let test expected term =
  let result = Format.asprintf "%a" S.pp_toplevel term in
  if result = expected then () else
    let () = Format.printf "Got: %s\nExpected: %s\n" result expected in
    failwith "Not what was expected"


let () = test "λ x y → x" (S.Lam (abs "x", S.Lam (abs "y", S.Var 1)))
let () = test "(λ x → x) (λ y → y)" (S.Ap (S.Lam (abs "x", S.Var 0), S.Lam (abs "y", S.Var 0)))
let () = test "(λ x → x , λ y → y)" (S.Pair (S.Lam (abs "x", S.Var 0), (S.Lam (abs "y", S.Var 0))))
let () = test "λ x → x x (x x)" (S.Lam (abs "x", S.Ap (S.Ap (S.Var 0, S.Var 0), S.Ap (S.Var 0, S.Var 0))))
(* BlockArguments is an extension :-/ *)
let () = test "λ x → x (λ y → x)" (S.Lam (abs "x", S.Ap (S.Var 0, S.Lam (abs "y", S.Var 1))))
let () = test "λ x → x (fst x x)" (S.Lam (abs "x", S.Ap (S.Var 0, S.Ap (S.Fst (S.Var 0), S.Var 0))))
let () = test "(x : Type) → λ x → x" (S.Pi (abs "x", S.Univ, S.Lam (abs "x", S.Var 0)))
let () = test "(x : λ y → y) × x" (S.Sigma (abs "x", S.Lam (abs "y", S.Var 0), S.Var 0))
let () = test "λ x → succ (succ x)" (S.Lam (abs "x", S.Succ (S.Succ (S.Var 0))))
let () = test "λ x → 2" (S.Lam (abs "x", S.Succ (S.Succ S.Zero)))
let () = Format.printf "All good!\n"
