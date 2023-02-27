open Bwd
open Bwd.Infix

type t = Data.value =
  | Neu of t * neu
  | Pi of Ident.t * t * clo
  | Lam of Ident.t * clo

and neu = Data.neu = { hd : hd; spine : frame bwd }        

and hd = Data.hd =
  | Var of int

and frame = Data.frame =
  | Ap of { tp : t; arg : t }

and env = t bwd
and clo = Data.clo = Clo of { env : env; body : Data.syn }

let push_frm {hd; spine} frm =
  {hd; spine = spine #< frm}
