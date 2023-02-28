open Core

module S = Syntax
open Ident

let () = print_newline ()
let () = S.pp_toplevel Format.std_formatter
  (S.Ap (S.Ap (S.Lam (user ["hola"], S.Lam (user ["hi"], S.Var 1)), (S.Lam (user ["there"], S.Var 0))), S.Ap (S.Lam (user ["world"], S.Var 0), S.Lam (user ["mundo"], S.Var 0))))
