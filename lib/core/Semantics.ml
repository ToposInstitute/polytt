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
    instrs : Data.instr list;
    (** The current program, used to perform reverse evaluation. *)
    cells : int;
    (** The number of memory cells required to execute the program. *)
  }
  module Env = Algaeff.Reader.Make (struct type nonrec env = env end)
  module Instrs = Algaeff.State.Make (struct type nonrec state = state end)

  let var ix =
    let env = Env.read () in
    Bwd.nth env ix

  let emit instr =
    Instrs.modify @@ fun st ->
    { st with instrs = instr :: st.instrs }

  (** Allocate [n] cells, and return the address of the first cell allocated. *)
  let allocate n =
    let st = Instrs.get () in
    Instrs.set { st with cells = st.cells + n };
    st.cells

  let clo (body : 'a) : 'a D.clo =
    let env = Env.read () in
    D.Clo { env; body }

  let append vs k =
    Env.scope (fun env -> Bwd.append env vs) k

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
    | S.Hom (p, q) ->
      D.Hom (eval p, eval q)
    | S.HomLam (p_name, q_name, bdy) ->
      D.HomLam (p_name, q_name, clo bdy) 
    | S.HomElim (hom, i) ->
      do_hom_elim (eval hom) (eval i)
    | S.Hole (tp, n) ->
      D.hole (eval tp) n

  (** Interpret a negative expression as a sequence of instructions.
      Returns the input address of the sequence of instructions. *)
  and eval_neg neg =
    match neg with
    | S.Var ix ->
      (* Calling convention: 0th cell is reserved for the final output
         of the instruction sequence. If we bind further variables
         (IE: by eliminating a tensor), then they will be in cells 1...n.
         This forces us to use DeBruijin levels for negative variables, even
         in the syntax. *)
      ix
    | S.NegAp (neg, fn) ->
      let read_addr = allocate 1 in
      let write_addr = eval_neg neg in
      emit @@ D.NegAp { write_addr; read_addr; fn = eval fn };
      read_addr
    | S.Drop ->
      allocate 1

  (** Calling convention: The value returned by [eval_hom]
      is the address to write the initial value to. *)
  and eval_hom steps =
    let rec eval_steps =
      function
      | S.Set (pos, neg, steps) ->
        let write_addr = eval_neg neg in
        emit @@ D.Const { write_addr; value = eval pos };
        eval_steps steps
      | S.HomAp (hom, pos, neg, _, _, steps) ->
        let read_addr = allocate 1 in
        let write_addr = eval_neg neg in
        let r = do_hom_elim (eval hom) (eval pos) in
        append [do_fst r] @@ fun () ->
        emit @@ D.NegAp { write_addr; read_addr; fn = do_snd r };
        eval_steps steps
      | S.Done (pos, neg) ->
        let in_addr = eval_neg neg in
        eval pos, in_addr
    in
    Instrs.run ~init:{ instrs = []; cells = 0 } @@ fun () ->
    let base, addr = eval_steps steps in
    let st = Instrs.get () in
    base, addr, st.instrs

  and eval_instr cells =
    function
    | D.Const { write_addr; value } ->
      CCVector.set cells write_addr (Some value)
    | D.NegAp { write_addr; read_addr; fn } ->
      let v = Option.get @@ CCVector.get cells read_addr in
      CCVector.set cells write_addr (Some (do_ap fn v))

  and eval_instrs addr instrs arg =
    let cells = CCVector.make (addr + 1) None in
    CCVector.set cells addr (Some arg);
    List.iter (eval_instr cells) instrs;
    Option.get @@ CCVector.get cells 0 

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_t, clo) ->
      inst_clo clo arg
    | D.FibLam (addr, instrs) ->
      eval_instrs addr instrs arg
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

  and do_hom_elim hom i =
    match hom with
    | D.HomLam (_, _, clo) ->
      inst_hom_clo clo i
    | D.Neu (D.Hom (p, q), neu) ->
      let p_base = do_base p in
      let fib =
        graft_value @@
        Graft.value p @@ fun p ->
        Graft.value q @@ fun q ->
        Graft.value p_base @@ fun p_base ->
        Graft.build @@
        TB.sigma (TB.base q) @@ fun q_base ->
        TB.pi (TB.fib q q_base) @@ fun _ -> TB.fib p p_base
      in
      D.Neu (fib, D.push_frm neu (D.HomElim { base = p_base; value = i }))
    | _ ->
      invalid_arg "bad do_hom_elim"

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) (fun () -> eval body)

  and inst_hom_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) @@ fun () ->
      let base, addr, instrs = eval_hom body in
      D.Pair (base, D.FibLam (addr, instrs))

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
