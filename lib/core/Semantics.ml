open Bwd
open Bwd.Infix

module S = Syntax
module D = Domain
module MS = Map.Make(String)

open TermBuilder

module Internal =
struct
  type env = D.env
  type state = {
    instrs : Data.instr bwd;
    (** The current program, used to perform reverse evaluation. *)
    cells : int;
    (** The number of memory cells required to execute the program. *)
  }
  module Env = Algaeff.Reader.Make (struct type nonrec env = env end)
  module Instrs = Algaeff.State.Make (struct type nonrec state = state end)

  let var ix =
    let env = Env.read () in
    Bwd.nth env ix

  let clo body =
    let env = Env.read () in
    D.Clo { env; body }

  let rec eval (tm : S.t) : D.t =
    match tm with
    | S.Var ix ->
      var ix
    | S.Pi (nm, a, b) ->
      D.Pi (nm, eval a, clo b)
    | S.Lam (nm, b) ->
      D.Lam (nm, clo b)
    | S.Let (_nm, tm1, tm2) ->
      inst_clo (clo tm2) (eval tm1)
    | S.Ap (f, a) ->
      do_ap (eval f) (eval a)
    | S.Sigma (nm, a, b) ->
      D.Sigma (nm, eval a, clo b)
    | S.Pair (a, b) ->
      D.Pair (eval a, eval b)
    | S.Fst tm ->
      do_fst (eval tm)
    | S.Snd tm ->
      do_snd (eval tm)
    | S.Nat ->
      D.Nat
    | S.Zero ->
      D.Zero
    | S.Succ n ->
      D.Succ (eval n)
    | S.NatElim {mot; zero; succ; scrut} ->
      do_nat_elim (eval mot) (eval zero) (eval succ) (eval scrut)
    | S.FinSet ls ->
      D.FinSet ls
    | S.Label (ls, l) ->
      D.Label (ls, l)
    | S.Cases (mot, cases, case) ->
      do_cases (eval mot) (List.map (fun (l, v) -> l, eval v) cases) (eval case)
    | S.Univ ->
      D.Univ
    | S.Poly ->
      D.Poly
    | S.PolyIntro (base, fib) ->
      D.PolyIntro (eval base, clo fib)
    | S.Base p ->
      do_base (eval p)
    | S.Fib (p, i) ->
      do_fib (eval p) (eval i)
    | S.Hole (tp, n) ->
      D.hole (eval tp) n

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_t, clo) ->
      inst_clo clo arg
    | D.Neu (Pi(_t, a, clo), neu) ->
      let fib = inst_clo clo arg in
      D.Neu (fib, D.push_frm neu (D.Ap { tp = a; arg }))
    | d ->
      Debug.print "Tried to do_ap against %a@." D.dump d;
      invalid_arg "bad do_ap"

  and do_aps f args =
    List.fold_left do_ap f args

  and do_fst (v: D.t) =
    match v with
    | D.Pair (a, _b) ->
      a
    | D.Neu (D.Sigma (_, a, _clo), neu) ->
      D.Neu (a, D.push_frm neu D.Fst)
    | _ ->
      invalid_arg "bad do_fst"

  and do_snd (v: D.t) =
    match v with
    | D.Pair (_a, b) ->
      b
    | D.Neu (D.Sigma (_, _a, clo), neu) ->
      let fib = inst_clo clo (do_fst v) in
      D.Neu (fib, D.push_frm neu D.Snd)
    | _ ->
      invalid_arg "bad do_snd"

  and do_cases mot cases case =
    match case with
    | D.Label (_, l) ->
      MS.find l (MS.of_seq (List.to_seq cases))
    | D.Neu (D.FinSet _, neu) ->
      let fib = do_ap mot case in
      D.Neu (fib, D.push_frm neu (D.Cases { mot; cases }))
    | d ->
      Debug.print "Tried to do_cases against %a@." D.dump d;
      invalid_arg "bad do_cases"

  and do_nat_elim mot zero succ scrut =
    let rec rec_nat_elim =
      function
      | D.Zero ->
        zero
      | D.Succ n ->
        do_aps succ [n; rec_nat_elim n]
      | D.Neu (_, neu) as n ->
        let fib = do_ap mot n in
        D.Neu (fib, D.push_frm neu (D.NatElim { mot; zero; succ }))
      | _ ->
        invalid_arg "bad do_nat_elim"
    in rec_nat_elim scrut

  and do_base p =
    match p with
    | D.PolyIntro (base, _) ->
      base
    | D.Neu (D.Poly, neu) ->
      D.Neu (D.Univ, D.push_frm neu D.Base)
    | _ ->
      invalid_arg "bad do_base"

  and do_fib p i =
    match p with
    | D.PolyIntro (_, fib) ->
      inst_clo fib i
    | D.Neu (D.Poly, neu) ->
      let base = do_base p in
      D.Neu (D.Univ, D.push_frm neu (D.Fib { base; value = i }))
    | _ ->
      invalid_arg "bad do_base"

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) (fun () -> eval body)

  and graft_value (gtm : S.t Graft.t) =
    let tm, env = Graft.graft gtm in
    Env.run ~env @@ fun () -> eval tm
end

let eval ~env tm =
  Internal.Env.run ~env @@ fun () ->
  Internal.eval tm

let eval_top tm =
  eval ~env:Emp tm

let do_ap =
  Internal.do_ap

let do_aps =
  Internal.do_aps

let do_fst =
  Internal.do_fst

let do_snd =
  Internal.do_snd

let do_base =
  Internal.do_base

let do_fib =
  Internal.do_fib

let do_nat_elim ~mot ~zero ~succ ~scrut =
  Internal.do_nat_elim mot zero succ scrut

let inst_clo =
  Internal.inst_clo

let graft_value =
  Internal.graft_value
