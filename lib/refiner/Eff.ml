open Bwd
open Bwd.Infix
open Core
open Errors

module D = Domain
module S = Syntax
module Sem = Semantics

open Ident

module IntSet = Set.Make (Int)

module Cell =
struct
  type pos = { name : Ident.t; tp : D.tp; value : D.t; }
  type neg = { name : Ident.t; tp : D.tp; lvl : int }

  type t =
    | Pos of pos
    | Neg of neg

  let name =
    function
    | Pos {name; _} -> name
    | Neg {name; _} -> name

  let value =
    function
    | Pos {value; _} -> value
    | Neg {tp; lvl; _} -> D.Neu (tp, { hd = D.Borrow lvl; spine = Emp })
end

module Globals =
struct
  type _ Effect.t += Resolve : Ident.path -> Global.t option Effect.t

  let resolve path =
    Effect.perform (Resolve path)

  let run ~(resolve : Ident.path -> Global.t option) k =
    Effect.Deep.try_with k () {
      effc =
        fun (type a) (eff : a Effect.t) ->
          match eff with
          | Resolve p ->
            Option.some @@ fun (k : (a, _) Effect.Deep.continuation) ->
            Algaeff.Fun.Deep.finally k (fun () -> resolve p)
          | _ -> None
    }
end

module Locals =
struct
  type env = {
    locals : D.t bwd;
    local_types : D.tp bwd;
    local_names : (Cell.t, unit) Yuujinchou.Trie.t;
    size : int;
    neg_size : int;
    (* Snoc list of whether this cell has been consumed, and its value (which
       will be written sometime after it is consumed) *)
    neg_values : (bool ref * D.t ref) bwd;
    neg_types : D.tp bwd;
    ppenv_pos : Ident.t bwd;
    ppenv_neg : Ident.t bwd
  }

  let top_env = {
    locals = Emp;
    local_types = Emp;
    local_names = Yuujinchou.Trie.empty;
    size = 0;
    neg_size = 0;
    neg_values = Emp;
    neg_types = Emp;
    ppenv_pos = Emp;
    ppenv_neg = Emp
  }

  let drop_linear env =
    { env with
      local_names = Yuujinchou.Trie.filter
          ( fun _ (cell, _) ->
              match cell with
              | Cell.Pos _ -> true
              | Cell.Neg _ -> false
          )
          env.local_names;
      neg_size = 0;
      neg_values = Emp;
      neg_types = Emp;
      ppenv_neg = Emp
    }

  module Reader = Algaeff.Reader.Make(struct type nonrec env = env end)

  let run_top k =
    Reader.run ~env:top_env k

  let all_consumed () =
    let env = Reader.read () in
    Bwd.for_all (fun (c, _) -> !c) env.neg_values

  let run_linear k =
    Reader.scope drop_linear @@ fun () ->
    k ()

  let env () =
    Reader.read ()

  let local_types () =
    let env = Reader.read () in
    env.local_types

  let ppenv () : S.ppenv =
    let env = Reader.read () in
    { pos = env.ppenv_pos; neg_size = env.neg_size; neg = env.ppenv_neg }

  let qenv () : QuoteEnv.t =
    let env = Reader.read () in
    { pos_size = env.size; neg_size = env.neg_size; neg = Bwd.map (fun (_, r) -> !r) env.neg_values }

  let denv () : D.env =
    let env = Reader.read () in
    { pos = env.locals; neg_size = env.neg_size; neg = env.neg_types }

  let size () =
    let env = Reader.read () in
    env.size

  let resolve path =
    let env = Reader.read () in
    Yuujinchou.Trie.find_singleton path env.local_names
    |> function
    | Some (Pos pos, ()) -> Some pos
    | _ -> None

  let resolve_neg path =
    let env = Reader.read () in
    Yuujinchou.Trie.find_singleton path env.local_names
    |> function
    | Some (Neg neg, ()) -> Some neg
    | _ -> None

  let fresh_var tp () =
    let env = Reader.read () in
    D.var tp env.size

  let fresh_neg_var () =
    let env = Reader.read () in
    env.neg_size

  let bind_var cell env =
    let local_names =
      match Cell.name cell with
      | `User path ->
        Yuujinchou.Trie.update_singleton path (fun _ -> Some (cell, ())) env.local_names
      | _ -> env.local_names
    in
    match cell with
    | Cell.Pos {name; value; tp} -> {
        env with
        locals = env.locals #< value;
        local_types = env.local_types #< tp;
        local_names;
        size = env.size + 1;
        ppenv_pos = env.ppenv_pos #< name
      }
    | Cell.Neg {name; lvl; tp} ->
      {
        env with
        local_names;
        neg_size = env.neg_size + 1;
        neg_types = env.neg_types #< tp;
        neg_values = env.neg_values #< (ref false, ref (D.Neu (tp, { hd = D.Borrow lvl; spine = Emp })));
        ppenv_neg = env.ppenv_neg #< name
      }

  let bind_transparent cell env =
    let local_names =
      match Cell.name cell with
      | `User path ->
        Yuujinchou.Trie.update_singleton path (fun _ -> Some (cell, ())) env.local_names
      | _ -> env.local_names
    in {
      env with local_names
    }

  let bind_vars cells env =
    List.fold_left (fun env cell -> bind_var cell env) env cells

  let concrete_ident ?(name = `Anon) tp tm k =
    let cell = Cell.Pos { name; tp; value = tm } in
    Reader.scope (bind_var cell) @@ fun () ->
    k ()

  let transparent_ident ?(name = `Anon) tp tm k =
    let cell = Cell.Pos { name; tp; value = tm } in
    Reader.scope (bind_transparent cell) @@ fun () ->
    k ()

  let abstract_ident ?(name = `Anon) tp k =
    let var = fresh_var tp () in
    let cell = Cell.Pos { name; tp; value = var } in
    Reader.scope (bind_var cell) @@ fun () ->
    k var

  let rec coalesce = function
  | Var (_, v) -> v
  | Tuple (l, r) ->
    let (lv) = coalesce l in
    let (rv) = coalesce r in
    D.Pair (lv, rv)

  let rec bind_tree ?(name = Var `Anon) tp tm k =
    begin match name with
    | Var ident ->
        transparent_ident ~name:ident tp tm
          (fun () -> k (Var (tp, tm)))
    | Tuple (l, r) ->
      begin match tp with
      | D.Sigma (_, a, clo) ->
        Debug.print "a: %a@." D.dump a;
        Debug.print "tm: %a@." D.dump tm;
        Debug.print "tm.1: %a@." D.dump (Sem.do_fst tm);
        Debug.print "tm.2: %a@." D.dump (Sem.do_snd tm);
        bind_tree ~name:l a (Sem.do_fst tm) @@ fun lvars ->
          bind_tree ~name:r (Sem.inst_clo clo (coalesce lvars)) (Sem.do_snd tm) @@ fun rvars ->
            Debug.print "bound@.";
            k (Tuple (lvars, rvars))
      | _ -> failwith "can only unpack a sigma" (* FIXME *)
      end
    end

  let concrete ?(name = Var `Anon) tp tm k =
    (* No need to bind a single anonymous variable *)
    begin match name with
    | Var ident -> concrete_ident ~name:ident tp tm @@ fun _ -> k (ident, (tp, tm), Var (tp, tm))
    | _ -> concrete_ident ~name:`Anon tp tm @@ fun _ -> bind_tree ~name tp tm @@ fun v -> k (`Anon, (tp, tm), v)
    end

  let abstract ?(name = Var `Anon) tp k =
    (* No need to bind a single anonymous variable *)
    begin match name with
    | Var ident -> abstract_ident ~name:ident tp @@ fun tm -> k (ident, (tp, tm), Var (tp, tm))
    | _ -> abstract_ident ~name:`Anon tp @@ fun tm -> bind_tree ~name tp tm @@ fun v -> k (`Anon, (tp, tm), v)
    end

  let abstract_neg_ident ?(name = `Anon) tp k =
    let lvl = fresh_neg_var () in
    let neg_cell = { Cell.name; tp; lvl } in
    let cell = Cell.Neg neg_cell in
    Reader.scope (bind_var cell) @@ fun () ->
    k lvl

  let consume_neg lvl () =
    let env = Reader.read () in
    let (consumed, value_ref) = Bwd.nth env.neg_values ((env.neg_size - 1) - lvl) in
    match !consumed with
    | true ->
      None
    | false ->
      consumed := true;
      Some (fun value -> value_ref := value)

  let rec split = function
  | Var (lvl, v) -> (Var lvl, v)
  | Tuple (l, r) ->
    let (ll, lv) = split l in
    let (rl, rv) = split r in
    (Tuple (ll, rl), D.Pair (lv, rv))

  let rec bind_neg_tree ?(name = Var `Anon) tp k =
    begin match name with
    | Var ident ->
      abstract_neg_ident ~name:ident tp @@
        fun lvl -> k (Var (lvl, D.Neu (tp, { hd = D.Borrow lvl; spine = Emp })))
    | Tuple (l, r) ->
      begin match tp with
      | D.Sigma (_, a, clo) ->
        bind_neg_tree ~name:l a @@ fun lvars ->
          Debug.print "ASDFASDFASFDSAFAS %a@." D.dump (snd (split lvars));
          bind_neg_tree ~name:r (Sem.inst_clo clo (snd (split lvars))) @@ fun rvars ->
            k (Tuple (lvars, rvars))
      | _ -> failwith "can only unpack a sigma" (* FIXME *)
      end
    end

  let abstract_neg ?(name = Var `Anon) tp k =
    (* No need to bind a single anonymous variable *)
    begin match name with
    | Var ident ->
      abstract_neg_ident ~name:ident tp @@ fun lvl ->
        k (ident, (tp, D.Neu (tp, { hd = D.Borrow lvl; spine = Emp })), Var lvl)
    | _ ->
      (* allocate 1 *)
      abstract_neg_ident ~name:`Anon tp @@ fun lvl ->
        (* allocate n *)
        bind_neg_tree ~name tp @@ fun lvls ->
          (* e.g. binding (p , q) *)
          match consume_neg lvl () with
          | None -> failwith "internal error (abstract_neg -> consume_neg)"
          | Some setter ->
            let (r, value) = split lvls in
            (* write 1 *)
            (* value = Sigma.intro (borrow p) (borrow q) *)
            setter value;
            (* allocated n+1 cells *)
            (* but net only n obligations *)
            k (`Anon, (tp, value), r)
    end

  (* Used in Prog.neg_lam/Prog.neg_lam_syn *)
  (* Calling convention: the most recently bound variable is abstract, of type i_tp *)
  (* Pass it a program to run, whose changes to context are recorded and
     replayed by writing a new value in place of the most recently bound
     variable which this is called *)
  (* If successful, this returns a sink, to replay the cb() with a new value *)
  let revert (_i_tp : D.tp) cb =
    (* save the environment before and after *)
    let env0 = Reader.read () in
    let already_used = Bwd.map2 (fun (used, _) tp -> !used, tp) env0.neg_values env0.neg_types in
    cb ();
    let env1 = Reader.read () in
    assert (env1.neg_size >= env0.neg_size);
    (* we quote the updated values in the current environment *)
    let q = qenv () in
    (* then we save the environment into the closure but with the most recent
       bound variable dropped *)
    let d = denv () in
    let ok = ref true in
    let reverted =
      (Bwd.mapi (fun i v -> i,v) env1.neg_values) |>
      Bwd.filter_map @@ fun (i, (used, value)) ->
      let used_now = !used in
      match Bwd.nth_opt already_used i with
      | None ->
        (* a sink that was allocated but not written to
           (and is now unable to be written to) *)
        if not used_now then ok := false;
        None
      (* a sink that was written to by cb() *)
      | Some (false, o_tp) when used_now ->
        (* we are going to quote the value and plop it into a closure, where
           the most recent bound variable gets dropped so that it will be
           overwritten when instantiating the closure *)
        Debug.print "o_tp: %a@.              %a@." D.dump o_tp S.dump (Quote.quote ~env:q ~tp:D.Univ o_tp);
        Debug.print "value: %a@." D.dump !value;
        let quoted = Quote.quote ~env:q ~tp:o_tp !value in
        Debug.print "       %a@." S.dump quoted;
        let dropped =
          match d.pos with
          | Snoc (pos, _) -> { d with pos = pos }
          | _ -> d
        in
        let abstracted : D.tm_clo = Clo { env = dropped; body = quoted } in
        Some (fun v -> value := Semantics.inst_clo abstracted v)
      (* an old sink (already existed), not newly written to *)
      | Some _ -> None
    in
    match !ok with
    | false -> None
    (* return a callback that applies all changes, but to the new value *)
    | true -> Some (fun value -> Bwd.iter (fun f -> f value) reverted)

  let abstracts ?(names = [Var `Anon]) tp k =
    let step name cont bounds =
        abstract ~name tp @@ fun bound -> cont (List.cons bound bounds)
    in List.fold_right step names k []
end


module Error =
struct
  module Eff = Algaeff.Reader.Make(struct type nonrec env = Span.t end)

  let error code fmt =
    let loc = Eff.read () in
    Logger.fatalf ~loc:loc code fmt

  let type_error tp conn =
    let loc = Eff.read () in
    let env = Locals.qenv () in
    let ppenv = Locals.ppenv () in
    let qtp = Quote.quote ~env ~tp:D.Univ tp in
    Logger.fatalf ~loc:loc `TypeError "Expected %a, but got %s@."
      (S.pp ppenv Precedence.isolated) qtp
      conn

  let locate loc k =
    Eff.scope (fun _ -> loc) k

  let run ~loc k =
    Eff.run ~env:loc k
end

module Hole =
struct
  module Eff = Algaeff.State.Make(struct type nonrec state = int end)
  let fresh () =
    let n = Eff.get () in
    Eff.set (n + 1);
    n

  let run k = Eff.run ~init:0 k
end

let quote ~tp tm =
  let env = Locals.qenv () in
  Quote.quote ~env ~tp tm

let equate ~tp v1 v2 =
  let env = Locals.qenv () in
  let ppenv = Locals.ppenv () in
  try
    Conversion.equate ~env ~tp v1 v2
  with Conversion.Unequal ->
    Debug.print "Unequal:@.%a@.%a@." D.dump v1 D.dump v2;
    let tm1 = Quote.quote ~env ~tp v1 in
    let tm2 = Quote.quote ~env ~tp v2 in
    Debug.print "Unequal:@.%a@.%a@." S.dump tm1 S.dump tm2;
    Error.error `ConversionError "@[<v 2>Could not solve:@ @[<v>%a@] = @[<v>%a@]@]"
      (S.pp ppenv (Precedence.left_of S.equals)) tm1
      (S.pp ppenv (Precedence.right_of S.equals)) tm2

let inst_const_clo ~tp clo =
  let env = Locals.qenv () in
  Skolem.inst_const_clo ~env ~tp clo

let eval tm =
  let env = Locals.denv () in
  Semantics.eval ~env tm

let inst_clo clo v =
  Semantics.inst_clo clo v

let graft_value gr =
  Semantics.graft_value gr

let do_ap f a =
  Semantics.do_ap f a

let do_fst tm =
  Semantics.do_fst tm

let do_snd tm =
  Semantics.do_snd tm

let do_nat_elim ~mot ~zero ~succ ~scrut =
  Semantics.do_nat_elim ~mot ~zero ~succ ~scrut

let do_base p =
  Semantics.do_base p

let do_fib p i =
  Semantics.do_fib p i

let do_hom_elim p i =
  Semantics.do_hom_elim p i
