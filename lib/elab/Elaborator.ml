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
    | _ ->
      T.Chk.syn (syn tm)

  and chk_lams names tm =
    match names with
    | [] -> chk tm
    | name :: names ->
      Pi.intro ~name @@ fun _ -> chk_lams names tm

  and syn (tm : CS.t) =
    Core.Debug.print "syn@.";
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | CS.Var path ->
      syn_var path
    (* R.Var.resolve path *)
    | CS.Univ ->
      Univ.formation
    | CS.Pi (names, a, b) ->
      Pi.formation ~names (chk a) (fun _ -> chk b)
    | CS.Ap (fn, args) ->
      List.fold_left (fun tac arg -> Pi.ap tac (chk arg)) (syn fn) args
    | CS.Let (nm, tm1, tm2) ->
      syn_let ~name:nm tm1 tm2
    | CS.Sigma (names, a, b) ->
      Sigma.formation ~names (chk a) (fun _ -> chk b)
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
    | CS.RecordLit cases ->
      FinSet.record_lit_syn (List.map (fun (l, v) -> l, syn v) cases)
    | _ ->
      T.Error.error `RequiresAnnotation "Term requires an annotation."

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
          T.Error.error `UnboundVariable "Variable is not bound."
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
