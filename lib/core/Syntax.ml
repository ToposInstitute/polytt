type t = Data.syn =
  | Var of int
  | Pi of Ident.t * t * t (* Π (a : A) (B a) *)
  | Lam of Ident.t * t (* λ x. e *)
  | Ap of t * t (* f a *)
