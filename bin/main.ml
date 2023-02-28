open Core

module S = Syntax
open Ident
open Refiner
open Tactic

let tp = Eff.run_top @@ fun () ->
  Chk.run (Pi.formation ~name:(`User ["A"]) Univ.formation @@ fun a -> Pi.formation ~name:(`User ["x"]) (Chk.syn @@ Var.syn a) @@ fun _ -> Chk.syn @@ Var.syn a) D.Univ

let () = S.pp_toplevel Format.std_formatter tp
(* let _ = Eff.run_top @@ fun () -> *)
(*   Chk.run __ __ *)
let () = print_newline ()
let () = S.pp_toplevel Format.std_formatter
    (S.Ap (S.Ap (S.Lam (user ["hola"], S.Lam (user ["hi"], S.Var 1)), (S.Lam (user ["there"], S.Var 0))), S.Ap (S.Lam (user ["world"], S.Var 0), S.Lam (user ["mundo"], S.Var 0))))
