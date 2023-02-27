open Bwd

type syn =
  | Var of int
  | Pi of Ident.t * syn * syn (* Π (a : A) (B a) *)
  | Lam of Ident.t * syn (* λ x. e *)
  | Ap of syn * syn (* f a *)
  | Univ

and value =
  | Neu of value * neu
  | Pi of Ident.t * value * clo
  | Lam of Ident.t * clo
  | Univ

and neu = { hd : hd; spine : frame bwd }        

and hd =
  | Var of int

and frame =
  | Ap of { tp : value; arg : value }

and env = value bwd
and clo = Clo of { env : env; body : syn }
