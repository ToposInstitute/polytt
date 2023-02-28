open Asai
open Core

type 'a node = { node : 'a; loc : Span.t }

type t = t_ node
and t_ =
  | Var of Yuujinchou.Trie.path
  | Pi of Ident.t * t * t
  | Lam of Ident.t list * t
  | Ap of t * t list
  | Sigma of Ident.t * t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Nat
  | Zero
  | Succ of t
  | NatElim of t * t * t * t
  | Lit of int
  | Univ
