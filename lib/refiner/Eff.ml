open Bwd
open Bwd.Infix
open Core
open Errors

module D = Domain
module S = Syntax

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
    CodeUnit.run @@ fun () ->
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

  let head () =
    let env = Reader.read () in
    if (env.neg_size == 0) then invalid_arg (Format.asprintf "Eff.Locals.head on empty context");
    ! (snd (Bwd.nth env.neg_values (env.neg_size - 1)))

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

  let bind_vars cells env =
    List.fold_left (fun env cell -> bind_var cell env) env cells

  let concrete ?(name = `Anon) tp tm k =
    let cell = Cell.Pos { name; tp; value = tm } in
    Reader.scope (bind_var cell) @@ fun () ->
    k ()

  let abstract ?(name = `Anon) tp k =
    let var = fresh_var tp () in
    let cell = Cell.Pos { name; tp; value = var } in
    Reader.scope (bind_var cell) @@ fun () ->
    k var

  let abstract_neg ?(name = `Anon) tp k =
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

  let revert i_tp cb =
    Debug.print "i_tp: %a@." D.dump i_tp;
    let env0 = Reader.read () in
    let already_used = Bwd.map2 (fun (used, _) tp -> !used, tp) env0.neg_values env0.neg_types in
    cb ();
    let env1 = Reader.read () in
    assert (env1.neg_size >= env0.neg_size);
    let q = qenv () in
    let d = denv () in
    let ok = ref true in
    let reverted =
      (Bwd.mapi (fun i v -> i,v) env1.neg_values) |>
      Bwd.filter_map @@ fun (i, (used, value)) ->
      let used_now = !used in
      match Bwd.nth_opt already_used i with
      | None ->
        if not used_now then ok := false;
        None
      | Some (false, o_tp) when used_now ->
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
      | Some _ -> None
    in
    match !ok with
    | false -> None
    | true -> Some
                (fun value -> Bwd.iter (fun f -> f value) reverted)

  let abstracts ?(names = [`Anon]) tp k =
    let cells =
      names
      |> List.mapi @@ fun i name ->
      (* TODO cleanup *)
      (Pos { Cell.name; tp; value = D.var tp ((Reader.read ()).size + i) } : Cell.t)
    in
    let vars = List.map Cell.value cells in
    Reader.scope (bind_vars cells) @@ fun () ->
    k vars
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
    Error.error `ConversionError "Could not solve %a = %a@."
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
