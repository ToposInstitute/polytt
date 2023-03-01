open Asai
open Core

type 'a node = { node : 'a; loc : Span.t }

type t = t_ node
and t_ =
  | Var of Ident.path
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
  | Poly
  | Base of t
  | Fib of t * t
  | PolyHom of t * t
  | PolyHomIntro of t * t
  | PolyHomLam of Ident.t * t
  | HomBase of t * t
  | HomFib of t * t * t * t
  | Tensor of t * t
  | TensorIntro of t * t
  | TensorElim of Ident.t * Ident.t * t * t * t
  | Tri of t * t
  | TriIntro of t * t
  | Frown of t * t * t
