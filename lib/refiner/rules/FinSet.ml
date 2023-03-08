open Core
open Tactic

module D = Domain
module S = Syntax
module Sem = Semantics
module SS = Set.Make(String)

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

let formation ls =
  Syn.rule @@ fun () ->
  if SS.cardinal (SS.of_list ls) != List.length ls then Error.error `TypeError "Duplicate finset labels";
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
  if SS.cardinal (SS.of_list ls) != List.length ls then Error.error `TypeError "Duplicate record labels";
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
  | D.Pi (nm, D.FinSet ls', clo) ->
    let ls = List.map fst cases_tac in
    if SS.cardinal (SS.of_list ls) != List.length ls then Error.error `TypeError "Duplicate record labels";
    if SS.equal (SS.of_list ls) (SS.of_list ls')
    then
      let mot_tp =
        graft_value @@
        Graft.build @@
        TB.pi ~name:nm (TB.finset ls') (fun _ -> TB.univ) in
      (* We bind an (anonymous) variable here, as we will be placing
         the cases underneath a lambda binder. *)
      let cases =
        cases_tac
        |> List.map @@
        function
        | l, case_tac ->
          l,
          Var.concrete (D.FinSet ls) (D.Label (ls, l)) @@ fun v ->
          Chk.run case_tac (Sem.inst_clo clo (Var.value v))
      in
      S.Lam ( Ident.anon,
              Locals.abstract (D.FinSet ls) @@ fun _ ->
              S.Cases (quote ~tp:mot_tp (D.Lam (nm, clo)), cases, S.Var 0)
            )
    else
      Error.error `TypeError "Record labels did not match expected type."
  | _ ->
    Error.error `TypeError "Expected element of record."

let record_lit_syn cases_tac =
  Syn.rule @@ fun () ->
  let ls = List.map fst cases_tac in
  (* We bind an (anonymous) variable here, as we will be placing
     the cases underneath a lambda binder. *)
  let cases_tp_tm =
    cases_tac
    |> List.map @@ fun (l, case_tac) ->
    l, Var.concrete (D.FinSet ls) (D.Label (ls, l)) @@ fun _ ->
    let tp, tm = Syn.run case_tac in
    let tp = quote ~tp:D.Univ tp in
    (tp, tm)
  in
  let cases_tp = List.map (fun (l, (tp, _)) -> l, tp) cases_tp_tm in
  let cases_tm = List.map (fun (l, (_, tm)) -> l, tm) cases_tp_tm in
  let mot_tp = S.Lam (Ident.anon, S.Univ) in
  let is_univ = fun (_, tp) -> tp = S.Univ in
  let thingy =
    (* FIXME bad hack *)
    if ((List.for_all is_univ cases_tp) && (List.exists is_univ cases_tp))
    then S.Univ
    else S.Cases (mot_tp, cases_tp, S.Var 0)
  in
  let mot = S.Lam (Ident.anon, thingy) in
  let tp = eval (S.Pi (Ident.anon, S.FinSet ls, thingy)) in
  tp , S.Lam (Ident.anon, S.Cases (mot, cases_tm, S.Var 0))
