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

let quote ~tp tm =
  let env = Locals.read () in
  Quote.quote ~size:env.size ~tp tm

let eval tm =
  let env = Locals.read () in
  Semantics.eval ~env:(Bwd.map Cell.value env.locals) tm

let inst_clo clo v =
  Semantics.inst_clo clo v

let fresh_var tp () =
  let env = Locals.read () in
  D.var tp env.size

let abstract ?(name = `Anon) tp k =
  let var = fresh_var tp () in
  let bind_var env =
    { locals = env.locals #< { name; tp; value = var };
      size = env.size + 1;
    }
  in
  Locals.scope bind_var @@ fun () ->
  k var
