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
  | Eq of t * t
  | Refl
  | Nat
  | Zero
  | Succ
  | NatElim of t * t * t * t
  | FinSet of labelset
  | Label of label
  | Record of t labeled
  | RecordLit of t labeled
  | Lit of int
  | Univ
  | NegPair of t * Ident.t * t
  | NegPairSimple of t * t
  | NegUnpack of t * t * Ident.t * Ident.t * t
  | NegUnpackSimple of t * Ident.t * Ident.t * t
  | Poly
  | Base of t
  | Fib of t * t
  | Hom of t * t
  | HomLam of Ident.t * Ident.t * t
  | Set of t * t * t
  | NegAp of t * t list
  | Drop
  | HomAp of t * t * t * Ident.t * Ident.t * t
  | Done of t * t
  | Anno of t * t (* (t : ty) *)
  | Hole
