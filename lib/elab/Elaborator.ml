module CS = Syntax
module D = Core.Domain
module S = Core.Syntax
module Sem = Core.Semantics
module Ident = Core.Ident

open Refiner
module T = Tactic

module Internal =
struct
  let rec chk (tm : CS.t) =
    T.Chk.locate tm.loc @@
    match tm.value with
    | CS.Lam (names, tm) ->
      chk_lams names tm
    | CS.LamSyn (qs, tm) ->
      List.fold_left
        (fun b (names, a) ms -> Pi.intro_chk ~names (chk a) (fun ns -> b (ms @ ns)))
        (fun _ -> chk tm)
        (List.rev qs)
        []
    | CS.Let (name, tm1, tm2) ->
      let tm1 = syn tm1 in
      Var.let_bind ~name:name tm1 (fun _ -> chk tm2)
    | CS.Sigma (qs, b) ->
      List.fold_right (fun (names, a) b -> chk_sigma ~names a b) qs (fun _ -> chk b) []
    | CS.Pair (a, b) ->
      Sigma.intro (chk a) (chk b)
    | CS.Refl ->
      Eq.intro
    | CS.Zero ->
      Nat.zero
    | CS.Succ ->
      Nat.succ
    | CS.Lit n ->
      Nat.lit n
    | CS.Hole ->
      (* call refiner hole rule *)
      Hole.unleash
    | CS.Label l ->
      FinSet.label l
    | CS.RecordLit cases ->
      FinSet.record_lit (List.map (fun (l, v) -> l, chk v) cases)
    | CS.Poly ->
      Poly.formation
    | CS.Repr ->
      Poly.repr_formation
    | CS.ReprIntro exp ->
      Poly.repr_intro (chk exp)
    | CS.HomLam (pos_name, neg_name, bdy) ->
      Hom.intro ~pos_name ~neg_name (fun _ _ -> hom bdy)
    | _ ->
      T.Chk.syn (syn tm)

  and neg_chk (tm : CS.t) =
    T.NegChk.locate tm.loc @@
    match tm.value with
    | CS.NegPair (a, name, b) ->
      NegSigma.intro (neg_chk a) ~name (fun _ -> neg_chk b)
    | CS.Drop ->
      Hom.drop
    | CS.NegPairSimple (p, q) ->
      NegSigma.intro_simple_chk (neg_chk p) (neg_chk q)
    | CS.NegLam (name, body) ->
      Prog.neg_lam ~name (fun _ -> prog body)
    | CS.Hole ->
      Hole.unleash_neg
    | _ ->
      T.NegChk.syn (neg_syn tm)

  and chk_lams names tm =
    match names with
    | [] -> chk tm
    | name :: names ->
      Pi.intro ~name @@ fun _ -> chk_lams names tm

  and chk_sigma ?(names = [Var `Anon]) a b _ =
    T.match_goal @@
    function
    | D.Univ -> T.Chk.syn @@ Sigma.formation ~names (chk a) b
    | D.Poly ->
      begin
        match names with
        | [name] -> Poly.intro ~name (chk a) (fun n -> b [n])
        | _ -> T.Error.error `TypeError "Polynomials only bind one name"
      end
    | _ -> T.Error.error `TypeError "Pair syntax only works for sigma and poly."

  and syn_univ b =
    T.Syn.ann (chk b) (T.Chk.syn Univ.formation)

  and syn (tm : CS.t) =
    T.Syn.locate tm.loc @@
    match tm.value with
    | CS.LamSyn (qs, tm) ->
      List.fold_left
        (fun b (names, a) ms -> Pi.intro_syn ~names (chk a) (fun ns -> b (ms @ ns)))
        (fun _ -> syn tm)
        (List.rev qs)
        []
    | CS.Var path ->
      syn_var path
    | CS.Univ ->
      Univ.formation
    | CS.Pi (qs, b) ->
      List.fold_left
        (fun b (names, a) ms -> Pi.formation ~names (chk a) (fun ns -> T.Chk.syn (b (ms @ ns))))
        (fun _ -> syn_univ b)
        (List.rev qs)
        []
    | CS.Ap (fn, args) ->
      syn_aps fn args
    | CS.Let (nm, tm1, tm2) ->
      syn_let ~name:nm tm1 tm2
    | CS.Sigma (qs, b) ->
      List.fold_left
        (fun b (names, a) ms -> Sigma.formation ~names (chk a) (fun ns -> T.Chk.syn (b (ms @ ns))))
        (fun _ -> syn_univ b)
        (List.rev qs)
        []
    | CS.Fst tm ->
      Sigma.fst (syn tm)
    | CS.Snd tm ->
      Sigma.snd (syn tm)
    | CS.Eq (a, b) ->
      Eq.formation (syn a) (chk b)
    | CS.Nat ->
      Nat.formation
    | CS.Zero ->
      Nat.zero_syn
    | CS.Succ ->
      Nat.succ_syn
    | CS.Lit n ->
      Nat.lit_syn n
    | CS.NatElim (mot, zero, succ, scrut) ->
      Nat.elim (chk mot) (chk zero) (chk succ) (syn scrut)
    | CS.Anno (tm, tp) ->
      T.Syn.ann (chk tm) (chk tp)
    | CS.Hole ->
      Hole.unleash_syn
    | CS.FinSet ls ->
      FinSet.formation ls
    | CS.Record cases ->
      FinSet.record (List.map (fun (l, v) -> l, chk v) cases)
    | CS.Base p ->
      Poly.base (chk p)
    | CS.Fib (p, i) ->
      Poly.fib (chk p) (chk i)
    | CS.Log r ->
      Poly.log (chk r)
    | CS.Hom (p, q) ->
      Hom.formation (chk p) (chk q)
    | CS.RecordLit cases ->
      FinSet.record_lit_syn (List.map (fun (l, v) -> l, syn v) cases)
    | CS.ReprIntro exp ->
      T.Syn.ann (Poly.repr_intro (chk exp)) Poly.repr_formation
    | _ ->
      T.Error.error `RequiresAnnotation "Cannot synth term, it requires an annotation."

  and neg_syn (tm : CS.t) =
    T.NegSyn.locate tm.loc @@
    match tm.value with
    | CS.Var path ->
      begin
        match T.Locals.resolve_neg path with
        | Some cell ->
          Var.negative cell
        | None ->
          T.Error.error `UnboundVariable "Variable is not bound (or not negative, idk)."
      end
    | CS.NegAp (neg, fns) ->
      List.fold_left (fun neg_tac fn -> Hom.neg_ap (T.NegChk.syn neg_tac) (syn fn)) (neg_syn neg) fns
    | CS.Drop ->
      T.Error.error `TypeError "Cannot synthesize type of drop."
    | CS.NegPairSimple (p, q) ->
      NegSigma.intro_simple (neg_syn p) (neg_syn q)
    | CS.NegLamSyn (name, tp, body) ->
      Prog.neg_lam_syn ~name (chk tp) (fun _ -> prog body)
    | CS.Hole ->
      Hole.unleash_neg_syn
    | _ ->
      T.Error.error `TypeError "Cannot synthesize (negative) type."

  and hom (tm : CS.t) =
    T.Hom.locate tm.loc @@
    match tm.value with
    | Set (pos, neg, steps) ->
      Hom.set (chk pos) (neg_syn neg) (hom steps)
    | HomAp (pos, neg, phi, pos_name, neg_name, steps) ->
      Hom.ap (chk pos) (neg_chk neg) (syn phi) ~pos_name ~neg_name (fun _ _ -> hom steps)
    | NegUnpack (scrut, a_name, b_name, body) ->
      NegSigma.elim (neg_syn scrut) ~a_name ~b_name (fun _ _ -> hom body)
    | Let (name, tm, body) ->
      Hom.pos_let ~name (syn tm) (fun _ -> hom body)
    | NegLet (name, tm, body) ->
      Hom.neg_let ~name (neg_syn tm) (fun _ -> hom body)
    | Return (pos, neg) ->
      Hom.done_ (chk pos) (neg_chk neg)
    | Hole ->
      Hole.unleash_hom
    | _ ->
      T.Error.error `NotAHom "Cannot be used to build a hom."

  and prog (tm : CS.t) =
    T.Prog.locate tm.loc @@
    match tm.value with
    | Set (pos, neg, steps) ->
      Prog.set (chk pos) (neg_syn neg) (prog steps)
    | HomAp (pos, neg, phi, pos_name, neg_name, steps) ->
      Prog.ap (chk pos) (neg_chk neg) (syn phi) ~pos_name ~neg_name (fun _ _ -> prog steps)
    (* TODO *)
    (* | NegUnpack (scrut, a_name, b_name, body) ->
       NegSigma.elim (neg_syn scrut) ~a_name ~b_name (fun _ _ -> prog body) *)
    | Let (name, tm, body) ->
      Prog.pos_let ~name (syn tm) (fun _ -> prog body)
    | NegLet (name, tm, body) ->
      Prog.neg_let ~name (neg_syn tm) (fun _ -> prog body)
    | Done ->
      Prog.end_
    | Hole ->
      Hole.unleash_prog
    | _ ->
      (* FIXME *)
      T.Error.error `NotAHom "Cannot be used to build a program."


  and syn_var path =
    match T.Locals.resolve path with
    | Some cell ->
      Refiner.Var.local cell
    | None ->
      begin
        match T.Globals.resolve path with
        | Some res ->
          Refiner.Var.global res
        | None ->
          Core.Debug.print "%a@." Ident.pp_path path;
          T.Error.error `UnboundVariable "Variable is not bound (or is negative, idk)."
      end

  and syn_let ~name tm1 tm2 =
    let tm1 = syn tm1 in
    T.Syn.rule @@ fun () ->
    let (vtp1, etm1) = T.Syn.run tm1 in
    let vtm = Eff.eval etm1 in
    let body = T.Chk.run (T.Var.concrete ~name vtp1 vtm (fun _ -> chk tm2)) vtp1 in
    (vtp1, body)

  and syn_ap fn arg =
    T.match_syn fn @@ fun fn_tac ->
    function
    | D.Pi _ ->
      Pi.ap fn_tac arg
    | D.Hom _ ->
      Hom.elim fn_tac arg
    | _ ->
      T.Error.error `TypeError "Tried to apply something that wasn't a function-like."

  and syn_aps fn args =
    List.fold_left (fun tac arg -> syn_ap tac (chk arg)) (syn fn) args
end

let chk (tm : CS.t) (tp : D.tp) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Chk.run (Internal.chk tm) tp

let syn (tm : CS.t) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Syn.run (Internal.syn tm)
