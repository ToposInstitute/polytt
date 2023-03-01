open Asai
open Bwd
open Bwd.Infix
open Core
open Errors

module D = Domain
module S = Syntax


module Cell =
struct
  type t = {
    name : Ident.t;
    tp : D.tp;
    value : D.t;
  }

  let name cell = cell.name
  let tp cell = cell.tp
  let value cell = cell.value
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

module Locals =
struct
  type env = {
    locals : D.t bwd;
    local_names : (Cell.t, unit) Yuujinchou.Trie.t;
    size : int;
    ppenv : Ident.t bwd
  }

  let top_env = {
    locals = Emp;
    local_names = Yuujinchou.Trie.empty;
    size = 0;
    ppenv = Emp
  }

  module Eff = Algaeff.Reader.Make(struct type nonrec env = env end)

  let run_top k =
    Eff.run ~env:top_env k

  let env () =
    Eff.read ()

  let locals () =
    let env = Eff.read () in
    Yuujinchou.Trie.to_seq_values env.local_names
    |> Seq.map fst
    |> List.of_seq

  let ppenv () =
    let env = Eff.read () in
    env.ppenv

  let size () =
    let env = Eff.read () in
    env.size

  let resolve path =
    let env = Eff.read () in
    Yuujinchou.Trie.find_singleton path env.local_names
    |> Option.map @@ fun (cell, ()) -> cell

  let fresh_var tp () =
    let env = Eff.read () in
    D.var tp env.size

  let bind_var cell env =
    let name = Cell.name cell in
    let value = Cell.value cell in
    let local_names =
      match name with
      | `User path ->
        Yuujinchou.Trie.update_singleton path (fun _ -> Some (cell, ())) env.local_names
      | _ -> env.local_names
    in {
      locals = env.locals #< value;
      local_names;
      size = env.size + 1;
      ppenv = env.ppenv #< name
    }

  let concrete ?(name = `Anon) tp tm k =
    let cell = { Cell.name; tp; value = tm } in
    Eff.scope (bind_var cell) @@ fun () ->
    k ()

  let abstract ?(name = `Anon) tp k =
    let var = fresh_var tp () in
    let cell = { Cell.name; tp; value = var } in
    Eff.scope (bind_var cell) @@ fun () ->
    k var
end

module Error =
struct
  module Eff = Algaeff.Reader.Make(struct type nonrec env = Span.t end)

  let error code fmt =
    let loc = Eff.read () in
    Logger.fatalf ~loc:loc code fmt

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
    let tm1 = Quote.quote ~size:env.size ~tp v1 in
    let tm2 = Quote.quote ~size:env.size ~tp v2 in
    Error.error `ConversionError "Could not solve %a = %a@."
      (S.pp env.ppenv (Precedence.left_of S.equals)) tm1
      (S.pp env.ppenv (Precedence.right_of S.equals)) tm2

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
