open Bwd

module S = Syntax
module D = Domain
module Sem = Semantics

type t = { pos_size : int; neg : D.t bwd; neg_size : int }
(** Here we do need negative values, and sizes for level<->index conversions *)
module Eff = Algaeff.Reader.Make (struct type env = t end)

let incr_pos env = { env with pos_size = env.pos_size + 1 }

let read_pos_size () = (Eff.read ()).pos_size

let read_neg_lvl lvl =
  let env = Eff.read () in
  Bwd.nth env.neg ((env.neg_size - 1) - lvl)

let empty = { pos_size = 0; neg = Emp; neg_size = 0 }
