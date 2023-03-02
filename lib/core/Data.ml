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
  | Let of Ident.t * syn * syn (* let x = e in t *)
  | Ap of syn * syn (* f a *)
  | Sigma of Ident.t * syn * syn (* Σ[ a ∈ A] (B a) *)
  | Pair of syn * syn (* A × B *)
  | Fst of syn
  | Snd of syn
  | Nat (* ℕ *)
  | Zero (* zero *)
  | Succ of syn (* succ n *)
  | NatElim of { mot : syn; zero : syn; succ : syn; scrut : syn }
  | FinSet of labelset (* #{ foo, bar } *)
  | Label of labelset * label (* .foo *)
  | Cases of syn * syn labeled * syn (* { foo = syn₁, bar = syn₂ } e *)
  | Univ (* A *)
  | Poly
  | PolyIntro of syn * syn
  | Base of syn
  | Fib of syn * syn
  | Hole of syn * int

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
  | PolyIntro of value * clo

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
  | Base
  | Fib of { base : value; value : value }

(** {1 Instructions} *)
and instr =
  | Const of { out_addr : int; value : value }
  (** Write [value] to [out_addr] *)
  | Ap of { out_addr : int; in_addr : int; fn : value }
  (** Read a value from [in_addr], apply [fn] to it,
      and write the resulting value to [out_addr] *)
  | Pair of { out_addr : int; fst_addr : int; snd_addr : int; }
  (** Read a pair of values from [fst_addr] and [snd_addr], and write their pair to [out_addr] *)

and env = value bwd
and clo = Clo of { env : env; body : syn }
