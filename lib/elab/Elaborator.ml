module CS = Syntax

module R = Refiner
module T = R.Tactic

module Internal =
struct
  let rec chk (tm : CS.t) =
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
      failwith "FIXME: better errors (requires annotation)"
end

let chk tm tp =
  R.Eff.run_top @@ fun () ->
  T.Chk.run (Internal.chk tm) tp

let syn tm =
  R.Eff.run_top @@ fun () ->
  T.Syn.run (Internal.syn tm)
