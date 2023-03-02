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
    begin
      match List.find_opt (fun x -> x = l) ls with
      | Some _ -> S.Label (ls, l)
      | None -> Error.error `TypeError "Label not in expected finset."
    end
  | _ ->
    Error.error `TypeError "Expected element of a finite set."

let record cases_tac =
  Syn.rule @@ fun () ->

  (* { a : Nat, b : bool } = (l : #{a,b}) -> { a = Nat, b = bool } l *)
  (* come up with the list of labels mentioned in the record type *)
  let ls = List.map fst cases_tac in
  (* the motive for the cases is going to be constant: type *)
  let mot = S.Lam (Ident.anon, S.Univ) in
  (* for each case, we check that it is a type. We do this in an extended
     context, as we will be placing the cases under a pi type during
     our manual eta-expansion. *)
  let cases =
    Var.abstract (D.FinSet ls) @@ fun _ ->
    List.map (fun (l, case_tac) -> l, Chk.run case_tac D.Univ) cases_tac
  in
  (* eta-expand *)
  (D.Univ, S.Pi (Ident.anon, S.FinSet ls, S.Cases (mot, cases, S.Var 0)))

let record_lit cases_tac =
  Chk.rule @@
  function
  | D.Pi (nm, D.FinSet ls, clo) as tp ->
    let ls' = List.map fst cases_tac in
    if ls = ls'
    then
      let mot = D.Lam (nm, clo) in
      (* We bind an (anonymous) variable here, as we will be placing
         the cases underneath a lambda binder. *)
      let cases =
        List.map (fun (l, case_tac) -> l,
                                       Var.concrete (D.FinSet ls) (D.Label (ls, l)) @@ fun v ->
                                       let x = (Sem.inst_clo clo (Var.value v)) in
                                       let r = Chk.run case_tac x in
                                       r) cases_tac in
      S.Lam (Ident.anon, S.Cases (quote ~tp mot, cases, S.Var 0))
    else
      Error.error `TypeError "Record labels did not match expected type."
  | _ ->
    Error.error `TypeError "Expected element of record."
