(** The definition of core ASTs. These need to be defined in the same
    module, as they are mutually recursive. See Syntax.ml and Domain.ml
    for repackaged versions. *)

open Bwd

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type syn =
  | Var of int
  | GlobalVar of string * int
  | Pi of Ident.t * syn * syn (* Π (a : A) (B a) *)
  | Lam of Ident.t * syn (* λ x. e *)
  | Let of Ident.t * syn * syn (* let x = e in t *)
  | Ap of syn * syn (* f a *)
  | Sigma of Ident.t * syn * syn (* Σ[ a ∈ A] (B a) *)
  | Pair of syn * syn (* A × B *)
  | Fst of syn
  | Snd of syn
  | Eq of syn * syn * syn
  | Refl of syn
  (* Axiom J
     J : {A : Type} {x : A}
      -> (P : (y : A) -> x = y -> Type)
      -> P x refl
      -> {y : A} (p : x = y)
      -> P y p
  *)
  (* | AxiomJ of  *)
  | Nat (* ℕ *)
  | Zero (* zero *)
  | Succ of syn (* succ n *)
  | NatElim of { mot : syn; zero : syn; succ : syn; scrut : syn }
  | FinSet of labelset (* #{ foo, bar } *)
  | Label of labelset * label (* .foo *)
  | Cases of syn * syn labeled * syn (* { foo = syn₁, bar = syn₂ } e *)
  | Univ (* A *)
  | Hole of syn * int

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * clo
  | Lam of Ident.t * clo
  | Sigma of Ident.t * value * clo
  | Pair of value * value
  | Eq of value * value * value
  | Refl of value
  | Nat
  | Zero
  | Succ of value
  | FinSet of labelset
  | Label of labelset * label
  | Univ

and neu = { hd : hd; spine : frame bwd }

and hd =
  | Var of int
  | Hole of value * int

and frame =
  | Ap of { tp : value; arg : value }
  | Fst
  | Snd
  | NatElim of { mot : value; zero : value; succ : value }
  | Cases of { mot : value; cases : (string * value) list }

and env = value bwd
and clo = Clo of { env : env; body : syn }
