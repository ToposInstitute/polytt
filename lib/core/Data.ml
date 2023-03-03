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
  | Hom of syn * syn
  | HomLam of Ident.t * Ident.t * hom_syn
  | HomElim of syn * syn
  | Hole of syn * int
  | Skolem of syn
  (** Used for ensuring that pi types are not dependent, see Skolem.ml *)

and neg_syn =
  | Var of int
  (** Variables are DeBruijn levels, even in the syntax! *)
  | NegAp of neg_syn * syn
  | Drop

and hom_syn =
  | Set of syn * neg_syn * hom_syn
  | HomAp of syn * syn * neg_syn * Ident.t * Ident.t * hom_syn
  | Done of syn * neg_syn

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * tm_clo
  | Lam of Ident.t * tm_clo
  | Sigma of Ident.t * value * tm_clo
  | Pair of value * value
  | Nat
  | Zero
  | Succ of value
  | FinSet of labelset
  | Label of labelset * label
  | Univ
  | Poly
  | PolyIntro of value * tm_clo
  | Hom of value * value
  | HomLam of Ident.t * Ident.t * hom_clo
  | FibLam of int * instr list
  (** A compiled program, created by reverse evaluation.
      When applied, place the argument in the address of the
      [int] parameter, execute the instructions, and then
      read off the outputs off the 0th cell. *)

and neu = { hd : hd; spine : frame bwd }

and hd =
  | Var of int
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
  | HomElim of { base : value; value : value }

(** {1 Instructions} *)
and instr =
  | Const of { write_addr : int; value : value }
  (** Write [value] to [write_addr] *)
  | NegAp of { write_addr : int; read_addr : int; fn : value }

and env = value bwd
and 'a clo = Clo of { env : env; body : 'a }
and tm_clo = syn clo
and hom_clo = hom_syn clo
