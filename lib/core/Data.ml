(** The definition of core ASTs. These need to be defined in the same 
    module, as they are mutually recursive. See Syntax.ml and Domain.ml 
    for repackaged versions. *)

open Bwd

type syn =
  | Var of int
  | Pi of Ident.t * syn * syn (* Π (a : A) (B a) *)
  | Lam of Ident.t * syn (* λ x. e *)
  | Ap of syn * syn (* f a *)
  | Sigma of Ident.t * syn * syn
  | Pair of syn * syn
  | Fst of syn
  | Snd of syn
  | Nat
  | Zero
  | Succ
  | NatElim of { mot : syn; zero : syn; succ : syn; scrut : syn }
  | Univ

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * clo
  | Lam of Ident.t * clo
  | Sigma of Ident.t * value * clo
  | Pair of value * value
  | Nat
  | Zero
  | Succ
  | Univ

and neu = { hd : hd; spine : frame bwd }        

and hd =
  | Var of int

and frame =
  | Ap of { tp : value; arg : value }
  | Fst
  | Snd
  | NatElim of { mot : value; zero : value; succ : value }

and env = value bwd
and clo = Clo of { env : env; body : syn }
