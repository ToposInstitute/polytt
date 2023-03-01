(** The definition of core ASTs. These need to be defined in the same
    module, as they are mutually recursive. See Syntax.ml and Domain.ml
    for repackaged versions. *)

open Bwd

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type syn =
  | Var of int
  | Pi of Ident.t * syn * syn (* Π (a : A) (B a) *)
  | Lam of Ident.t * syn (* λ x. e *)
  | Ap of syn * syn (* f a *)
  | Sigma of Ident.t * syn * syn (* Σ[ a ∈ A] (B a) *)
  | Pair of syn * syn (* A × B *)
  | Fst of syn
  | Snd of syn
  | Nat (* ℕ *)
  | Zero
  | Succ of syn
  | NatElim of { mot : syn; zero : syn; succ : syn; scrut : syn }
  | FinSet of labelset
  | Label of labelset * label
  | Cases of syn * syn labeled * syn
  | Univ (* A *)
  | Poly
  | PolyIntro of syn * syn
  | Base of syn
  | Fib of syn * syn
  | PolyHom of syn * syn
  | PolyHomIntro of syn * syn
  | PolyHomLam of Ident.t * syn
  | HomBase of syn * syn * syn
  | HomFib of syn * syn * syn * syn
  | Tensor of syn * syn
  | TensorIntro of syn * syn
  | TensorElim of syn * syn * syn
  | Tri of syn * syn
  | TriIntro of syn * syn
  | Frown of syn * syn * syn

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * clo
  | Lam of Ident.t * clo
  | Sigma of Ident.t * value * clo
  | Pair of value * value
  | Nat
  | Zero
  | Succ of value
  | FinSet of labelset
  | Label of labelset * label
  | Univ
  | Poly
  | PolyIntro of value * value
  | PolyHom of value * value
  | PolyHomIntro of value * value
  | PolyHomLam of Ident.t * clo
  | Tensor of value * value
  | TensorIntro of value * value
  | Tri of value * value
  | TriIntro of value * value
  | Frown of value * value * value

and neu = { hd : hd; spine : frame bwd }

and hd =
  | Var of int

and frame =
  | Ap of { tp : value; arg : value }
  | Fst
  | Snd
  | NatElim of { mot : value; zero : value; succ : value }
  | Cases of { mot : value; cases : (string * value) list }
  | Base
  | Fib of { tp : value; base : value }
  | HomBase of { poly : value; base : value }
  | HomFib of { poly : value; base : value; fib : value }
  | TensorElim of { p : value; q : value; mot : value; bdy : clo }

and env = value bwd
and clo = Clo of { env : env; body : syn }
