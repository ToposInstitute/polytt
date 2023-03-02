open Core
open Errors
open Tactic
open TermBuilder

module D = Domain
module S = Syntax
module Sem = Semantics

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

let formation ls =
  Syn.rule @@ fun () ->
    (D.Univ, S.FinSet ls)

let label l =
  Chk.rule @@
  function
  | D.FinSet ls ->
    S.Label (ls, l)
  | _ ->
    Error.error `TypeError "Expected element of a finite set."

let record cases_tac =
  Syn.rule @@ fun () ->
    (* { a : Nat, b : bool } = (l : #{a,b}) -> { a = Nat, b = bool } l *)
    (* come up with the list of labels mentioned in the record type *)
    let ls = List.map fst cases_tac in
    (* the motive for the cases is going to be constant: type *)
    let mot = S.Lam (Ident.anon, S.Univ) in
    (* for each case, we check that it is a type *)
    let cases = List.map (fun (l, case_tac) -> l, Chk.run case_tac D.Univ) cases_tac in
    (* eta-expand *)
    (D.Univ, S.Pi (Ident.anon, S.FinSet ls, S.Cases (mot, cases, S.Var 0)))

let record_lit cases_tac =
  Chk.rule @@
  function
  | D.Pi (nm, D.FinSet ls, clo) as tp ->
    let mot = D.Lam (nm, clo) in
    let cases = List.map (fun (l, case_tac) -> l, Chk.run case_tac (Sem.inst_clo clo (D.Label (ls, l)))) cases_tac in
    S.Lam (Ident.anon, S.Cases (quote ~tp mot, cases, S.Var 0))
  | _ ->
    Error.error `TypeError "Expected element of record."