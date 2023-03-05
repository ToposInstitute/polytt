open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics
module SS = Set.Make(String)
module MS = Map.Make(String)

open TermBuilder

exception Unequal

module Internal =
struct
  module Eff = Algaeff.Reader.Make (struct type env = int end)

  let bind tp f =
    let arg = D.var tp @@ Eff.read() in
    Eff.scope (fun size -> size + 1) @@ fun () ->
      match tp with
      | D.FinSet ls when ls != [] ->
        begin
          try f arg with
          | Unequal ->
            Debug.print "CC FinSet ETA@.";
            Eff.scope (fun size -> size + 1) @@ fun () ->
              ls |> List.iter @@ fun l ->
                f (D.Label (ls, l))
        end
      | _ ->
        f arg

  let rec equate tp v1 v2 =
    match (tp, v1, v2) with
    | _, D.Neu (_, neu1), D.Neu (_, neu2) ->
      equate_neu neu1 neu2
    | _, D.Pi (_, a1, clo1), D.Pi (_, a2, clo2) ->
      equate D.Univ a1 a2;
      bind a1 @@ fun v ->
      equate D.Univ (Sem.inst_clo clo1 v) (Sem.inst_clo clo2 v);
      ()
    | D.Pi (_, a, clo), v1, v2 ->
      bind a @@ fun x ->
      let fib = Sem.inst_clo clo x in
      equate fib (Sem.do_ap v1 x) (Sem.do_ap v2 x)
    | _, D.Sigma (_, a1, clo1), D.Sigma (_, a2, clo2) ->
      equate D.Univ a1 a2;
      bind a1 @@ fun v ->
      equate D.Univ (Sem.inst_clo clo1 v) (Sem.inst_clo clo2 v)
    | D.Sigma (_, a, clo), v1, v2 ->
      equate a (Sem.do_fst v1) (Sem.do_fst v2);
      let fib = Sem.inst_clo clo v1 in
      equate fib (Sem.do_snd v1) (Sem.do_snd v2)
    | _, D.Nat, D.Nat ->
      ()
    | _, D.Zero, D.Zero ->
      ()
    | _, D.Succ n1, D.Succ n2 ->
      equate D.Nat n1 n2
    | _, D.FinSet s1, D.FinSet s2 when SS.equal (SS.of_list s1) (SS.of_list s2) ->
      ()
    | _, D.Label (_, l), D.Label (_, r) when l = r ->
      ()
    | _, D.Univ, D.Univ ->
      ()
    | _, D.NegUniv, D.NegUniv ->
      ()
    | _, D.NegSigma (_, a1, b1), D.NegSigma (_, a2, b2) ->
      equate D.Univ a1 a2;
      bind a1 @@ fun v ->
      equate D.Univ (Sem.inst_clo b1 v) (Sem.inst_clo b2 v)
    | _, D.Poly, D.Poly ->
      ()
    | D.Poly, v1, v2 ->
      let base1 = Sem.do_base v1 in
      let base2 = Sem.do_base v2 in
      equate D.Univ base1 base2;
      bind base1 @@ fun i ->
      equate D.Univ (Sem.do_fib v1 i) (Sem.do_fib v2 i)
    | _, D.Hom (p1, q1), D.Hom (p2, q2) ->
      equate D.Poly p1 p2;
      equate D.Poly q1 q2;
    | _, _, _ ->
      Debug.print "Could not equate %a and %a@."
        D.dump v1
        D.dump v2;
      raise Unequal

  and equate_neu (neu1 : D.neu) (neu2 : D.neu) =
    equate_hd neu1.hd neu2.hd;
    try Bwd.iter2 equate_frm neu1.spine neu2.spine
    with Invalid_argument _ -> raise Unequal

  and equate_hd hd1 hd2 =
    match hd1, hd2 with
    | D.Var lvl1, D.Var lvl2 when lvl1 = lvl2 ->
      ()
    | D.Hole (_, n) , D.Hole (_, m) when n = m ->
      ()
    | D.Skolem _, D.Skolem _ ->
      (* Skolems don't equate with themselves. This is used
         in the skolem check, as we equate something with itself to
         flush out any skolems. *)
      raise Unequal
    | D.Negate tp1, D.Negate tp2 ->
      equate D.Univ tp1 tp2
    | _ ->
      Debug.print "Could not equate heads.@.";
      raise Unequal

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
    | D.NatElim elim1, D.NatElim elim2 ->
      let mot_tp =
        Sem.graft_value @@
        Graft.build @@
        TB.pi TB.nat @@ fun _ -> TB.univ
      in
      equate mot_tp elim1.mot elim2.mot;
      equate (Sem.do_ap elim1.mot D.Zero) elim1.zero elim2.zero;
      let succ_tp =
        Sem.graft_value @@
        Graft.value elim1.mot @@ fun mot ->
        Graft.build @@
        TB.pi TB.nat @@ fun n ->
        TB.pi (TB.ap mot n) @@ fun _ ->
        TB.ap mot (TB.succ n)
      in
      equate succ_tp elim1.succ elim2.succ
    | D.Cases r1, D.Cases r2 ->
      (* This is not the bad eta law (c.f.
         http://strictlypositive.org/Ripley.pdf section 3: The Uniqueness of
         Magic), since we are only are matching on explicit case expressions
         here, and two empty ones will be definitionally equal already *)
      (* ls1 and ls2 are potentially different order, but by the end they should
         be checked to be identical, since their labels should correspond
         to the labels on their cases which we are checking *)
      let ls1 = List.map fst r1.cases in
      let ls2 = List.map fst r2.cases in
      let apply_motives l = (Sem.do_ap r1.mot (D.Label (ls1, l)), Sem.do_ap r2.mot (D.Label (ls2, l))) in
      let m1 = MS.of_seq (List.to_seq r1.cases) in
      let m2 = MS.of_seq (List.to_seq r2.cases) in
      let _ = equate_maps apply_motives m1 m2 in
      ()
    | D.Base, D.Base ->
      ()
    | D.Fib fib1, D.Fib fib2 ->
      equate fib1.base fib1.value fib2.value
    | D.HomElim {tp; value = v1}, D.HomElim {value = v2; _} ->
      equate tp v1 v2
    | D.UnNegate, D.UnNegate ->
      ()
    | _ ->
      Debug.print "Could not equate frames %a and %a@."
        D.dump_frm frm1
        D.dump_frm frm2;
      raise Unequal

  and equate_maps apply_motives =
    MS.merge @@ fun k mv1 mv2 ->
    match mv1, mv2 with
    | Some v1, Some v2 ->
      let (m1, m2) = apply_motives k in
      equate D.Univ m1 m2;
      equate m1 v1 v2;
      None
    | _, _ -> raise Unequal
end

let equate ~size ~tp v1 v2 =
  Internal.Eff.run ~env:size @@ fun () ->
  Internal.equate tp v1 v2
