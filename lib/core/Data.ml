(** The definition of core ASTs. These need to be defined in the same
    module, as they are mutually recursive. See Syntax.ml and Domain.ml
    for repackaged versions. *)

open Bwd

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type syn =
  | Var of int
  | Global of Global.t
  | Borrow of int
  (** Negative variables are DeBruijn levels, even in the syntax! *)
  | Pi of Ident.t * syn * syn
  | Lam of Ident.t * syn
  | Let of Ident.t * syn * syn
  | Ap of syn * syn
  | Sigma of Ident.t * syn * syn
  | Pair of syn * syn
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
  | Nat
  | Zero
  | Succ of syn
  | NatElim of { mot : syn; zero : syn; succ : syn; scrut : syn }
  | FinSet of labelset
  | Label of labelset * label
  | Cases of syn * syn labeled * syn
  | Univ
  | Poly
  | PolyIntro of Ident.t * syn * syn
  | Repr
  | ReprIntro of syn
  | Base of syn
  | Fib of syn * syn
  | Log of syn
  | Hom of syn * syn
  | HomLam of syn
  | HomElim of syn * syn
  | Hole of syn * int
  | Skolem of syn
  (** Used for ensuring that pi types are not dependent, see Skolem.ml *)

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * tm_clo
  | Lam of Ident.t * tm_clo
  | Sigma of Ident.t * value * tm_clo
  | Pair of value * value
  | Eq of value * value * value
  | Refl of value
  | Nat
  | Zero
  | Succ of value
  | FinSet of labelset
  | Label of labelset * label
  | Univ
  | Poly
  | PolyIntro of Ident.t * value * tm_clo
  | Repr
  | ReprIntro of value
  | Hom of value * value
  | HomLam of value

and neu = { hd : hd; spine : frame bwd }

and hd =
  | Var of int
  | Borrow of int
  | Hole of value * int
  | Skolem of value

and frame =
  | Ap of { tp : value; arg : value }
  | Fst
  | Snd
  | NatElim of { mot : value; zero : value; succ : value }
  | Cases of { mot : value; cases : (string * value) list }
  | Base
  | Fib of { base : value; value : value }
  | Log
  | HomElim of { tp : value; arg : value }

and env = { pos : value bwd; neg_size : int; neg : value bwd }

(** We need to evaluate positive values, but we only borrow negatives so we just
    need their types, and we pass the size for quicker level<->index conversion *)
and 'a clo = Clo of { env : env; body : 'a }
and tm_clo = syn clo
