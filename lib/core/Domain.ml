(** The values of the core language.
    This module repackages definitions in Data.ml for nicer qualified imports. *)

open Bwd
open Bwd.Infix

module S = Syntax

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type t = Data.value =
  | Neu of t * neu
  | Pi of Ident.t * t * clo
  | Lam of Ident.t * clo
  | Sigma of Ident.t * t * clo
  | Pair of t * t
  | Eq of t * t * t
  | Refl of t
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

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

let rec dump fmt =
  function
  | Neu (t, neu) -> Format.fprintf fmt "neu[%a %a]" dump t dump_neu neu
  | Pi (nm, a, b) -> Format.fprintf fmt "pi[%a %a %a]" Ident.pp nm dump a dump_clo b
  | Sigma (nm, a, b) -> Format.fprintf fmt "sigma[%a %a %a]" Ident.pp nm dump a dump_clo b
  | Pair (a, b) -> Format.fprintf fmt "pair[%a %a]" dump a dump b
  | Lam (nm, t) -> Format.fprintf fmt "lam[%a, %a]" Ident.pp nm dump_clo t
  | Eq (t, a, b) -> Format.fprintf fmt "eq[%a, %a, %a]" dump t dump a dump b
  | Refl (a) -> Format.fprintf fmt "refl[%a]" dump a
  | Nat -> Format.fprintf fmt "nat"
  | Zero -> Format.fprintf fmt "zero"
  | Succ n -> Format.fprintf fmt "succ[%a]" dump n
  | FinSet ls -> Format.fprintf fmt "finset[%a]" (pp_sep_list Format.pp_print_string) ls
  | Label (ls, l) -> Format.fprintf fmt "label[%a, %a]" (pp_sep_list Format.pp_print_string) ls Format.pp_print_string l
  | Univ -> Format.fprintf fmt "univ"

and dump_neu fmt { hd = Var i; spine } =
  Format.fprintf fmt "D.var[%i %a]" i dump_spine spine

(* TODO *)
and dump_spine fmt spine = Format.fprintf fmt "$SPINE"

(* TODO *)
and dump_clo fmt (Clo { env; body }) = Format.fprintf fmt "$ENV %a" S.dump body
