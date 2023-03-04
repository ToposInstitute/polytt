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
  let allocate () =
    Debug.print "Allocating cell@.";
    let st = Instrs.get () in
    Instrs.set { st with cells = st.cells + 1 };
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
    | S.Eq (t, a, b) ->
      D.Eq (eval t, eval a, eval b)
    | S.Refl (a) ->
      D.Refl (eval a)
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
    | S.NegUniv ->
      D.NegUniv
    | S.Negate tp ->
      do_negate (eval tp)
    | S.UnNegate tp ->
      undo_negate (eval tp)
    | S.NegSigma (name, a, b_neg) ->
      D.NegSigma (name, eval a, clo b_neg)
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
    | S.Skolem tp ->
      D.skolem (eval tp)

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
      Debug.print "Encountered variable, read_addr is %d@." ix;
      ix
    | S.NegAp (neg, fn) ->
      let read_addr = allocate () in
      let write_addr = eval_neg neg in
      emit @@ D.NegAp { write_addr; read_addr; fn = eval fn };
      read_addr
    | S.NegPair (a_neg, _, b_neg) ->
      let read_addr = allocate () in
      let write_addr = eval_neg a_neg in
      emit @@ D.Unpair { read_addr; write_addr; clo = clo b_neg };
      read_addr
    | S.Drop ->
      Debug.print "Encountered drop@.";
      allocate ()

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
        let read_addr = allocate () in
        let write_addr = eval_neg neg in
        let r = do_hom_elim (eval hom) (eval pos) in
        append [do_fst r] @@ fun () ->
        emit @@ D.NegAp { write_addr; read_addr; fn = do_snd r };
        eval_steps steps
      | S.Unpack {scrut; case; _} ->
        (* We will write a pair to the address of scrut. *)
        let write_addr = eval_neg scrut in
        (* Body of the case has 2 free variables, so we need to allocate 2 cells. *)
        let read_fst_addr = allocate () in
        let read_snd_addr = allocate () in
        emit @@ D.Pack { write_addr; read_fst_addr; read_snd_addr };
        eval_steps case
      | S.Done (pos, neg) ->
        let in_addr = eval_neg neg in
        eval pos, in_addr
    in
    Instrs.run ~init:{ instrs = []; cells = 1 } @@ fun () ->
    let base, addr = eval_steps steps in
    let st = Instrs.get () in
    Debug.print "Compiled program, requires %d cells to evalute, initial addr %d@." st.cells addr;
    base, { D.addr; capacity = st.cells; instrs = st.instrs }

  and eval_instr cells =
    function
    | D.Const { write_addr; value } ->
      Debug.print "Running CONST at %d@." write_addr;
      CCVector.set cells write_addr (Some value)
    | D.NegAp { write_addr; read_addr; fn } ->
      let v = Option.get @@ CCVector.get cells read_addr in
      Debug.print "Running NEG AP at %d@." write_addr;
      CCVector.set cells write_addr (Some (do_ap fn v))
    | D.Unpair { read_addr; write_addr; clo } ->
      Debug.print "Running UNPAIR.@.";
      let v = Option.get @@ CCVector.get cells read_addr in
      let v1 = do_fst v in
      let v2 = do_snd v in
      CCVector.set cells write_addr (Some v1);
      inst_neg_clo cells clo v1 v2
    | D.Pack { write_addr; read_fst_addr; read_snd_addr } ->
      let a = Option.get @@ CCVector.get cells read_fst_addr in
      let b = Option.get @@ CCVector.get cells read_snd_addr in
      CCVector.set cells write_addr (Some (D.Pair (a, b)))

  and eval_prog (prog : D.prog) arg =
    let cells = CCVector.make prog.capacity None in
    Debug.print "Evaluating Program:@.%a@." D.dump_instrs prog.instrs;
    Debug.print "Writing Initial value at %d@." prog.addr;
    CCVector.set cells prog.addr (Some arg);
    List.iter (eval_instr cells) prog.instrs;
    Debug.print "Reading final value from 0.@.";
    Option.get @@ CCVector.get cells 0 

  and do_ap (f : D.t) (arg : D.t) =
    match f with
    | D.Lam (_t, clo) ->
      inst_clo clo arg
    | D.FibLam prog ->
      eval_prog prog arg
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

  and do_negate tp =
    match tp with
    | D.Sigma (name, a, clo) ->
      graft_value @@
      Graft.value a @@ fun a ->
      Graft.clo clo @@ fun b ->
      Graft.build @@
      TB.neg_sigma ~name a @@ fun x ->
      TB.negate (TB.ap b x)
    | D.Neu (D.Univ, { hd; spine = Snoc(spine, D.UnNegate) }) ->
      D.Neu (D.NegUniv, { hd; spine })
    | _ ->
      D.negate tp

  and undo_negate tp =
    match tp with
    | D.NegSigma (name, a, clo) ->
      graft_value @@
      Graft.value a @@ fun a ->
      Graft.clo clo @@ fun b ->
      Graft.build @@
      TB.sigma ~name a @@ fun x ->
      TB.unnegate (TB.ap b x)
    | D.Neu (D.NegUniv, { hd = D.Negate tp; spine = Emp } ) ->
      tp
    | D.Neu (D.NegUniv, neu) ->
      D.Neu (D.Univ, D.push_frm neu D.UnNegate)
    | _ ->
      invalid_arg "bad undo_negate"

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
      D.Neu (fib, D.push_frm neu (D.HomElim { tp = p_base; value = i }))
    | _ ->
      invalid_arg "bad do_hom_elim"

  and inst_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) (fun () -> eval body)

  and inst_neg_clo cells clo v arg =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) @@ fun () ->
      let orig_length = CCVector.length cells in
      let prog =
        Instrs.run ~init:{ instrs = []; cells = orig_length } @@ fun () ->
        let addr = eval_neg body in
        let st = Instrs.get () in
        { D.addr; capacity = st.cells; instrs = st.instrs }
      in
      CCVector.append cells (CCVector.make (prog.capacity - orig_length) None);
      CCVector.set cells prog.addr (Some arg);
      List.iter (eval_instr cells) prog.instrs;
      CCVector.truncate cells orig_length;

  and inst_hom_clo clo v =
    match clo with
    | D.Clo { env; body } ->
      Env.run ~env:(env #< v) @@ fun () ->
      let base, prog = eval_hom body in
      D.Pair (base, D.FibLam prog)

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

let do_negate =
  Internal.do_negate

let undo_negate =
  Internal.undo_negate

let do_base =
  Internal.do_base

let do_fib =
  Internal.do_fib

let do_nat_elim ~mot ~zero ~succ ~scrut =
  Internal.do_nat_elim mot zero succ scrut

let inst_clo =
  Internal.inst_clo

let inst_hom_clo =
  Internal.inst_hom_clo

let graft_value =
  Internal.graft_value
