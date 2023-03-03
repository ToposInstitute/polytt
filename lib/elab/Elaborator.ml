module CS = Syntax
module D = Core.Domain
module S = Core.Syntax
module Sem = Core.Semantics

open Refiner
module T = Tactic

module Internal =
struct
  let rec chk (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | CS.Lam (names, tm) ->
      chk_lams names tm
    | CS.Let (name, tm1, tm2) ->
      let tm1 = syn tm1 in
      Var.let_bind ~name:name tm1 (fun _ -> chk tm2)
    | CS.Sigma (name, a, b) ->
      chk_sigma ~name a b
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
    | CS.HomLam (pos_name, neg_name, bdy) ->
      Hom.intro ~pos_name ~neg_name (fun _ _ -> hom bdy)
    | _ ->
      T.Chk.syn (syn tm)

  and neg_chk (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    T.NegChk.syn (neg_syn tm)

  and chk_lams names tm =
    match names with
    | [] -> chk tm
    | name :: names ->
      Pi.intro ~name @@ fun _ -> chk_lams names tm

  and chk_sigma ?(name = `Anon) a b =
    T.match_goal @@
    function
    | D.Univ -> T.Chk.syn @@ Sigma.formation ~name (chk a) (fun _ -> chk b)
    | D.Poly -> Poly.intro ~name (chk a) (fun _ -> chk b)
    | _ -> T.Error.error `TypeError "Pair syntax only works for sigma and poly."

  and syn (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | CS.Var path ->
      syn_var path
    | CS.Univ ->
      Univ.formation
    | CS.Pi (name, a, b) ->
      Pi.formation ~name (chk a) (fun _ -> chk b)
    | CS.Ap (fn, args) ->
      List.fold_left (fun tac arg -> Pi.ap tac (chk arg)) (syn fn) args
    | CS.Let (nm, tm1, tm2) ->
      syn_let ~name:nm tm1 tm2
    | CS.Sigma (name, a, b) ->
      Sigma.formation ~name (chk a) (fun _ -> chk b)
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
      T.Error.error `HoleInSynth "Cannot synthesize type of hole."
    | CS.FinSet ls ->
      FinSet.formation ls
    | CS.Record cases ->
      FinSet.record (List.map (fun (l, v) -> l, chk v) cases)
    | CS.Base p ->
      Poly.base (chk p)
    | CS.Fib (p, i) ->
      Poly.fib (chk p) (chk i)
    | CS.Hom (p, q) ->
      Hom.formation (chk p) (chk q)
    | CS.RecordLit cases ->
      FinSet.record_lit_syn (List.map (fun (l, v) -> l, syn v) cases)
    | _ ->
      T.Error.error `RequiresAnnotation "Term requires an annotation."

  and neg_syn (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
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
    | _ ->
      T.Error.error `TypeError "Not a negative thingy."

  and hom (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | Set (pos, neg, steps) ->
      Hom.set (syn pos) (neg_chk neg) (hom steps)
    | HomAp (pos, neg, phi, pos_name, neg_name, steps) ->
      Hom.ap (chk pos) (neg_chk neg) (syn phi) ~pos_name ~neg_name (fun _ _ -> hom steps)
    | Done (pos, neg) ->
      Hom.done_ (chk pos) (neg_chk neg)
    | _ ->
      T.Error.error `NotAHom "Cannot be used to build a hom."


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
          T.Error.error `UnboundVariable "Variable is not bound (or is negative, idk)."
      end

  and syn_let ~name tm1 tm2 =
    let tm1 = syn tm1 in
    T.Syn.rule @@ fun () ->
    let (vtp1, etm1) = T.Syn.run tm1 in
    let vtm = Eff.eval etm1 in
    let body = T.Chk.run (T.Var.concrete ~name vtp1 vtm (fun _ -> chk tm2)) vtp1 in
    (vtp1, body)
end

let chk (tm : CS.t) (tp : D.tp) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Chk.run (Internal.chk tm) tp

let syn (tm : CS.t) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Syn.run (Internal.syn tm)
