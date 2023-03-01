module CS = Syntax
module D = Core.Domain
module S = Core.Syntax

open Refiner
module T = Tactic

module Internal =
struct
  let rec chk (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | CS.Pi (name, a, b) ->
      Pi.formation ~name (chk a) (fun _ -> chk b)
    | CS.Lam (names, tm) ->
      chk_lams names tm
    | CS.Sigma (name, a, b) ->
      Sigma.formation ~name (chk a) (fun _ -> chk b)
    | CS.Pair (a, b) ->
      chk_pair a b
    | CS.Nat ->
      Nat.formation
    | CS.Zero ->
      Nat.zero
    | CS.Succ n ->
      Nat.succ (chk n)
    | CS.Lit n ->
      Nat.lit n
    | CS.Univ ->
      Univ.formation
    | CS.Poly ->
      Poly.formation
    | CS.PolyHom (p, q) ->
      PolyHom.formation (chk p) (chk q)
    | CS.Tensor (p, q) ->
      Tensor.formation (chk p) (chk q)
    | CS.Tri (p, q) ->
      Tri.formation (chk p) (chk q)
    | CS.Frown (p, q, f) ->
      Frown.formation (chk p) (chk q) (chk f)
    | _ ->
      T.Chk.syn (syn tm)

  and chk_lams names tm =
    match names with
    | [] -> chk tm
    | name :: names ->
      T.match_goal @@
      function
      | D.Pi _ ->
        Pi.intro ~name @@ fun _ -> chk_lams names tm
      | D.PolyHom _ ->
        PolyHom.lam ~name @@ fun _ -> chk_lams names tm
      | _ ->
        T.Error.error `TypeError "Can only use lambda notation to make a Pi or a Hom."

  and chk_pair (a : CS.t) (b : CS.t) =
    T.match_goal @@
    function
    | D.Sigma _ ->
      Sigma.intro (chk a) (chk b)
    | D.Poly ->
      Poly.intro (chk a) (chk b)
    | D.PolyHom _ ->
      PolyHom.intro (chk a) (chk b)
    | D.Tensor _ ->
      Tensor.intro (chk a) (chk b)
    | _ ->
      T.Error.error `TypeError "Can only use pair notation to make a sigma, poly, or tensor."

  and syn (tm : CS.t) =
    T.Error.locate tm.loc @@ fun () ->
    match tm.node with
    | CS.Var path ->
      syn_var path
    | CS.Ap (fn, args) ->
      List.fold_left (fun tac arg -> Pi.ap tac (chk arg)) (syn fn) args
    | CS.Fst tm ->
      Sigma.fst (syn tm)
    | CS.Snd tm ->
      Sigma.fst (syn tm)
    | CS.NatElim (mot, zero, succ, scrut) ->
      Nat.elim (chk mot) (chk zero) (chk succ) (syn scrut)
    | CS.Base p ->
      Poly.base (chk p)
    | CS.Fib (p, x) ->
      Poly.fib (chk p) (chk x)
    | CS.HomBase (f, x) ->
      PolyHom.base (syn f) (chk x)
    | CS.HomFib (f, base, fib) ->
      PolyHom.fib (syn f) (chk base) (chk fib)
    | CS.TensorElim (p_name, q_name, mot, bdy, scrut) ->
      Tensor.elim ~p_name ~q_name (chk mot) (fun _ _ -> chk bdy) (syn scrut)
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
end

let chk (tm : CS.t) (tp : D.tp) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Chk.run (Internal.chk tm) tp

let syn (tm : CS.t) =
  T.Locals.run_top @@ fun () ->
  T.Error.run ~loc:tm.loc @@ fun () ->
  T.Syn.run (Internal.syn tm)
