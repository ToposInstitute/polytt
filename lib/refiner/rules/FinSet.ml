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
  Chk.rule @@
  function
  | D.Univ ->
    S.FinSet ls
  | _ ->
    Error.error `TypeError "Expected element of type."

let label l =
  Chk.rule @@
  function
  | D.FinSet ls ->
    S.Label (ls, l)
  | _ ->
    Error.error `TypeError "Expected element of a finite set."

let record cases_tac =
  Chk.rule @@
  function
  | D.Univ ->
    (* { a : Nat, b : bool } = (l : #{a,b}) -> { a = Nat, b = bool } l *)
    (* come up with the list of labels mentioned in the record type *)
    let ls = List.map fst cases_tac in
    (* the motive for the cases is going to be constant: type *)
    let mot = S.Pi (Ident.anon, S.FinSet ls, S.Univ) in
    (* for each case, we check that it is a type *)
    let cases = List.map (fun (l, case_tac) -> l, Chk.run case_tac D.Univ) cases_tac in
    (* eta-expand *)
    S.Pi (Ident.anon, S.FinSet ls, S.Cases (mot, cases, S.Var 0))
  | _ ->
    Error.error `TypeError "Expected element of type."

let record_lit cases_tac =
  Chk.rule @@
  function
  | D.Pi (_, D.FinSet ls, clo) as mot ->
    let cases = List.map (fun (l, case_tac) -> l, Chk.run case_tac (Sem.inst_clo clo (D.Label (ls, l)))) cases_tac in
    S.Lam (Ident.anon, S.Cases (quote ~tp:D.Univ mot, cases, S.Var 0))
  | _ ->
    Error.error `TypeError "Expected element of record."
