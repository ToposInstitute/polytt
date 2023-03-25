open Asai
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
end



module Globals =
struct
  type resolved =
    | Def of { tm : D.t; tp : D.tp }

  type _ Effect.t += Resolve : Ident.path -> resolved option Effect.t

  let resolve path =
    Effect.perform (Resolve path)

  let run ~(resolve : Ident.path -> resolved option) k =
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

module Linearity =
struct
  module State = Algaeff.State.Make(struct type nonrec state = IntSet.t end)

  let run k =
    State.run ~init:IntSet.empty @@ fun () ->
    let a = k () in
    let can_use = State.get () in
    if IntSet.is_empty can_use then
      Some a
    else
      None

  let obligation (neg : Cell.neg) =
    State.modify @@ fun can_use ->
    IntSet.add neg.lvl can_use

  let consume (neg : Cell.neg) =
    let can_use = State.get () in
    let available = IntSet.mem neg.lvl can_use in
    State.set @@ IntSet.remove neg.lvl can_use;
    not available
end

module Locals =
struct
  type env = {
    locals : D.t bwd;
    local_types : D.tp bwd;
    local_names : (Cell.t, unit) Yuujinchou.Trie.t;
    size : int;
    neg_size : int;
    ppenv : Ident.t bwd
  }

  let top_env = {
    locals = Emp;
    local_types = Emp;
    local_names = Yuujinchou.Trie.empty;
    size = 0;
    neg_size = 0;
    ppenv = Emp
  }

  module Reader = Algaeff.Reader.Make(struct type nonrec env = env end)

  let run_top k =
    Reader.run ~env:top_env k

  let env () =
    Reader.read ()

  let local_types () =
    let env = Reader.read () in
    env.local_types

  let ppenv () =
    let env = Reader.read () in
    env.ppenv

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
        ppenv = env.ppenv #< name
      }
    | Cell.Neg _ ->
      {
        env with
        local_names;
        neg_size = env.neg_size + 1;
        (* FIXME: Update the negative ppenv *)
      }

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
    Linearity.obligation neg_cell;
    Reader.scope (bind_var cell) @@ fun () ->
    k lvl
end


module Error =
struct
  module Eff = Algaeff.Reader.Make(struct type nonrec env = Span.t end)

  let error code fmt =
    let loc = Eff.read () in
    Logger.fatalf ~loc:loc code fmt

  let type_error tp conn =
    let loc = Eff.read () in
    let size = Locals.size () in
    let ppenv = Locals.ppenv () in
    let qtp = Quote.quote ~size:size ~tp:D.Univ tp in
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
  let env = Locals.env () in
  Quote.quote ~size:env.size ~tp tm

let equate ~tp v1 v2 =
  let env = Locals.env () in
  try
    Conversion.equate ~size:env.size ~tp v1 v2
  with Conversion.Unequal ->
    Debug.print "Unequal:@.%a@.%a@." D.dump v1 D.dump v2;
    let tm1 = Quote.quote ~size:env.size ~tp v1 in
    let tm2 = Quote.quote ~size:env.size ~tp v2 in
    Debug.print "Unequal:@.%a@.%a@." S.dump tm1 S.dump tm2;
    Error.error `ConversionError "Could not solve %a = %a@."
      (S.pp env.ppenv (Precedence.left_of S.equals)) tm1
      (S.pp env.ppenv (Precedence.right_of S.equals)) tm2

let inst_const_clo ~tp clo =
  let env = Locals.env () in
  Skolem.inst_const_clo ~size:env.size ~tp clo

let eval tm =
  let env = Locals.env () in
  Semantics.eval ~env:env.locals tm

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
