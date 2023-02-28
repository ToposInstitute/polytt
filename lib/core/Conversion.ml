open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics

exception Unequal

module Internal =
struct
  module Eff = Algaeff.Reader.Make (struct type env = int end)

  let bind tp f =
    let arg = D.var tp @@ Eff.read() in
    Eff.scope (fun size -> size + 1) @@ fun () ->
    f arg

  let rec equate tp v1 v2 = 
    match (tp, v1, v2) with
    | _, D.Neu (_, neu1), D.Neu (_, neu2) ->
      equate_neu neu1 neu2
    | _, D.Pi (_, a1, clo1), D.Pi (_, a2, clo2) ->
      equate D.Univ a1 a2;
      bind D.Univ @@ fun v ->
      equate D.Univ (Sem.inst_clo clo1 v) (Sem.inst_clo clo2 v)
    | D.Pi (_, a, clo), v1, v2 ->
      bind a @@ fun x ->
      let fib = Sem.inst_clo clo x in
      equate fib (Sem.do_ap v1 x) (Sem.do_ap v2 x)
    | _, D.Sigma (_, a1, clo1), D.Sigma (_, a2, clo2) ->
      equate D.Univ a1 a2;
      bind D.Univ @@ fun v ->
      equate D.Univ (Sem.inst_clo clo1 v) (Sem.inst_clo clo2 v)
    | D.Sigma (_, a, clo), v1, v2 ->
      equate a (Sem.do_fst v1) (Sem.do_fst v2);
      let fib = Sem.inst_clo clo v1 in
      equate fib (Sem.do_snd v1) (Sem.do_snd v2)
    | _, D.Univ, D.Univ -> ()
    | _, _, _ ->
      raise Unequal

  and equate_neu (neu1 : D.neu) (neu2 : D.neu) =
    equate_hd neu1.hd neu2.hd;
    try Bwd.iter2 equate_frm neu1.spine neu2.spine
    with Invalid_argument _ -> raise Unequal

  and equate_hd hd1 hd2 =
    match hd1, hd2 with
    | D.Var lvl1, D.Var lvl2 when lvl1 = lvl2 ->
      ()
    | _ -> raise Unequal

  and equate_frm frm1 frm2 =
    match frm1, frm2 with
    | D.Ap ap1, D.Ap ap2 ->
      (* Don't need to equate the argument types of 2 stuck applications,
         as our invariants require that all terms are well-typed. *)
      equate ap1.tp ap1.arg ap2.arg
    | D.Fst, D.Fst ->
      ()
    | D.Snd, D.Snd ->
      ()
    | _ ->
      raise Unequal
end

let equate ~size ~tp v1 v2 =
  Internal.Eff.run ~env:size @@ fun () ->
  Internal.equate tp v1 v2
