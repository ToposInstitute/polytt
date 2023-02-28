open Bwd
open Bwd.Infix
open Core

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
  size : int
}

module Locals = Algaeff.Reader.Make(struct type nonrec env = env end)

let run_top k =
  Locals.run ~env:{ locals = Emp; size = 0 } k

let quote ~tp tm =
  let env = Locals.read () in
  Quote.quote ~size:env.size ~tp tm

let equate ~tp v1 v2 =
  let env = Locals.read () in
  Conversion.equate ~size:env.size ~tp v1 v2

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
    { locals = env.locals #< { name; tp; value = var };
      size = env.size + 1;
    }
  in
  Locals.scope bind_var @@ fun () ->
  k var
