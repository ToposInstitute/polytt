module CS = Syntax
module D = Core.Domain
module S = Core.Syntax

module R = Refiner
module T = R.Tactic

module Internal =
struct
  let rec chk (tm : CS.t) =
    R.Eff.located tm.loc @@ fun () ->
    match tm.node with
    | CS.Pi (name, a, b) ->
      R.Pi.formation ~name (chk a) (fun _ -> chk b)
    | CS.Lam (name, tm) ->
      R.Pi.intro ~name (fun _ -> chk tm)
    | CS.Sigma (name, a, b) ->
      R.Sigma.formation ~name (chk a) (fun _ -> chk b)
    | CS.Pair (a, b) ->
      R.Sigma.intro (chk a) (chk b)
    | CS.Nat ->
      R.Nat.formation
    | CS.Zero ->
      R.Nat.zero
    | CS.Succ n ->
      R.Nat.succ (chk n)
    | CS.Lit n ->
      R.Nat.lit n
    | CS.Univ ->
      R.Univ.formation
    | _ ->
      T.Chk.syn (syn tm)

  and syn (tm : CS.t) =
    R.Eff.located tm.loc @@ fun () ->
    match tm.node with
    | CS.Var path ->
      R.Var.resolve (`User path)
    | CS.Ap (fn, args) ->
      List.fold_left (fun tac arg -> R.Pi.ap tac (chk arg)) (syn fn) args
    | CS.Fst tm ->
      R.Sigma.fst (syn tm)
    | CS.Snd tm ->
      R.Sigma.fst (syn tm)
    | CS.NatElim (mot, zero, succ, scrut) ->
      R.Nat.elim (chk mot) (chk zero) (chk succ) (syn scrut)
    | _ ->
      R.Eff.error `RequiresAnnotation "Term requires an annotation."
end

let chk (tm : CS.t) (tp : D.tp) =
  R.Eff.run_top ~loc:tm.loc @@ fun () ->
  T.Chk.run (Internal.chk tm) tp

let syn (tm : CS.t) =
  R.Eff.run_top ~loc:tm.loc @@ fun () ->
  T.Syn.run (Internal.syn tm)
