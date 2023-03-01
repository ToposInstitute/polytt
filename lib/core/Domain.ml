(** The values of the core language.
    This module repackages definitions in Data.ml for nicer qualified imports. *)

open Bwd
open Bwd.Infix

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type t = Data.value =
  | Neu of t * neu
  | Pi of Ident.t * t * clo
  | Lam of Ident.t * clo
  | Sigma of Ident.t * t * clo
  | Pair of t * t
  | Nat
  | Zero
  | Succ of t
  | FinSet of labelset
  | Label of labelset * label
  | Univ

and tp = t

and neu = Data.neu = { hd : hd; spine : frame bwd }

and hd = Data.hd =
  | Var of int
  | Hole of tp * int

and frame = Data.frame =
  | Ap of { tp : t; arg : t }
  | Fst
  | Snd
  | NatElim of { mot : t; zero : t; succ : t }
  | Cases of { mot : t; cases : t labeled }

and env = t bwd
and clo = Data.clo = Clo of { env : env; body : Data.syn }

let push_frm {hd; spine} frm =
  {hd; spine = spine #< frm}

let var tp lvl =
  Data.Neu (tp, { hd = Var lvl; spine = Emp })

let hole tp n =
  Data.Neu (tp, { hd = Hole (tp, n); spine = Emp })
