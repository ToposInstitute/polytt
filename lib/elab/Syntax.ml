open Asai
open Core

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type 'a node = { node : 'a; loc : Span.t }

type t = t_ node
and t_ =
  | Var of Yuujinchou.Trie.path
  | Pi of Ident.t * t * t
  | Lam of Ident.t list * t
  | Let of Ident.t * t * t
  | Ap of t * t list
  | Sigma of Ident.t * t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Nat
  | Zero
  | Succ of t
  | NatElim of t * t * t * t
  | FinSet of labelset
  | Label of label
  | Record of t labeled
  | RecordLit of t labeled
  | Lit of int
  | Univ
  | Poly
  | Base of t
  | Fib of t * t
  | Anno of t * t (* (t : ty) *)
  | Hole
