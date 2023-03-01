open Core
open Errors
open Tactic
open TermBuilder

module D = Domain
module S = Syntax

let formation =
  Syn.rule @@ fun () ->
    (D.Univ, S.Nat)

let zero =
  Chk.rule @@
  function
  | D.Nat ->
    S.Zero
  | _ ->
    Error.error `TypeError "Expected element of ℕ."

let succ tac =
  Chk.rule @@
  function
  | D.Nat ->
    S.Succ (Chk.run tac D.Nat)
  | _ ->
    Error.error `TypeError "Expected element of ℕ."

let lit n =
  Chk.rule @@
  function
  | D.Nat ->
    let rec go =
      begin
        function
        | 0 -> S.Zero
        | n -> S.Succ (go (n - 1))
      end
    in go n
  | t ->
    Debug.print "%a@." D.dump t;
    Error.error `TypeError "Expected element of ℕ."

let elim mot_tac zero_tac succ_tac scrut_tac =
  Syn.rule @@ fun () ->
  let mot_tp =
    graft_value @@
    Graft.build @@
    TB.pi TB.nat @@ fun _ -> TB.univ
  in
  let mot = Chk.run mot_tac mot_tp in
  let vmot = eval mot in
  let zero = Chk.run zero_tac (do_ap vmot D.Zero) in
  let succ_tp =
    graft_value @@
    Graft.value vmot @@ fun mot ->
    Graft.build @@
    TB.pi TB.nat @@ fun n ->
    TB.pi (TB.ap mot n) @@ fun _ ->
    TB.ap mot (TB.succ n)
  in
  let succ = Chk.run succ_tac succ_tp in
  let scrut_tp, scrut = Syn.run scrut_tac in
  let vscrut = eval scrut in
  match scrut_tp with
  | D.Nat ->
    do_ap vmot vscrut, S.NatElim {mot; zero; succ; scrut}
  | _ ->
    Error.error `TypeError "Expected element of nat."
