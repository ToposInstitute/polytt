open Asai
open Core

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type 'a node = { node : 'a; loc : Span.t }

type t = t_ node
and t_ =
  | Var of Yuujinchou.Trie.path
  | Pi of (Ident.binder list * t) list * t
  | Lam of Ident.binder list * t
  | LamSyn of (Ident.binder * t) list * t
  | Let of Ident.binder * t * t
  | Ap of t * t list
  | Sigma of (Ident.binder list * t) list * t
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
  | NegPair of t * Ident.binder * t
  | NegPairSimple of t * t
  | NegUnpack of t * Ident.binder * Ident.binder * t
  | Poly
  | Base of t
  | Fib of t * t
  | Hom of t * t
  | HomLam of Ident.binder * Ident.binder * t
  | Set of t * t * t
  | NegAnno of t * t
  | NegLet of Ident.binder * t * t
  | NegLam of Ident.binder * t
  | NegLamSyn of Ident.binder * t * t
  | NegAp of t * t list
  | Drop
  | Done
  | HomAp of t * t * t * Ident.binder * Ident.binder * t
  | Return of t * t
  | Anno of t * t (* (t : ty) *)
  | Hole
