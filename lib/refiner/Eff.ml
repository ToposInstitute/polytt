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

  let value cell =
    cell.value
end

type env = {
  locals : Cell.t bwd;
  size : int;
  loc : Span.t;
  ppenv : Ident.t bwd
}

module Locals = Algaeff.Reader.Make(struct type nonrec env = env end)

let run_top ~loc k =
  Locals.run ~env:{ locals = Emp; size = 0; loc; ppenv = Emp } k

let located loc k =
  Locals.scope (fun env -> { env with loc }) k

let error code fmt =
  let env = Locals.read () in
  Logger.fatalf ~loc:env.loc code fmt

let quote ~tp tm =
  let env = Locals.read () in
  Quote.quote ~size:env.size ~tp tm

let equate ~tp v1 v2 =
  let env = Locals.read () in
  try
    Conversion.equate ~size:env.size ~tp v1 v2
  with Conversion.Unequal ->
    let tm1 = Quote.quote ~size:env.size ~tp v1 in
    let tm2 = Quote.quote ~size:env.size ~tp v2 in
    error `ConversionError "Could not solve %a = %a@."
      (S.pp env.ppenv (Precedence.left_of S.equals)) tm1
      (S.pp env.ppenv (Precedence.right_of S.equals)) tm2

let eval tm =
  let env = Locals.read () in
  Semantics.eval ~env:(Bwd.map Cell.value env.locals) tm

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

let fresh_var tp () =
  let env = Locals.read () in
  D.var tp env.size

let lookup_var nm = 
  let env = Locals.read () in
  env.locals |> Bwd.find_opt @@ fun { Cell.name; _ } ->
  Ident.equal nm name

let abstract ?(name = `Anon) tp k =
  let var = fresh_var tp () in
  let bind_var env =
    { env with
      locals = env.locals #< { name; tp; value = var };
      size = env.size + 1;
      ppenv = env.ppenv #< name
    }
  in
  Locals.scope bind_var @@ fun () ->
  k var
