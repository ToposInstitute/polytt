(** The syntax of the core language.
    This module repackages definitions in Data.ml for nicer qualified imports. *)

open Bwd
open Bwd.Infix

module P = Precedence

type t = Data.syn =
  | Var of int
  | Pi of Ident.t * t * t (* Π (a : A) (B a) *)
  | Lam of Ident.t * t (* λ x. e *)
  | Ap of t * t (* f a *)
  | Sigma of Ident.t * t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Nat
  | Zero
  | Succ of t
  | NatElim of { mot : t; zero : t; succ : t; scrut : t }
  | Univ

(** Raw printing for debugging *)
let rec dump fmt =
  function
  | Univ -> Format.fprintf fmt "univ"
  | Var i -> Format.fprintf fmt "var[%i]" i
  | Pi (nm, a, b) -> Format.fprintf fmt "pi[%a %a %a]" Ident.pp nm dump a dump b
  | Sigma (nm, a, b) -> Format.fprintf fmt "sigma[%a %a %a]" Ident.pp nm dump a dump b
  | Pair (a, b) -> Format.fprintf fmt "pair[%a %a]" dump a dump b
  | Fst a -> Format.fprintf fmt "pair[%a]" dump a
  | Snd a -> Format.fprintf fmt "pair[%a]" dump a
  | Lam (nm, t) -> Format.fprintf fmt "lam[%a, %a]" Ident.pp nm dump t
  | Ap (f, a) -> Format.fprintf fmt "ap[%a, %a]" dump f dump a
  | Nat -> Format.fprintf fmt "nat"
  | Zero -> Format.fprintf fmt "zero"
  | Succ n -> Format.fprintf fmt "succ[%a]" dump n
  | NatElim r -> Format.fprintf fmt "nat-elim[%a %a %a %a]" dump r.mot dump r.zero dump r.succ dump r.scrut

let to_numeral =
  let rec go acc =
    function
    | Zero -> acc
    | Succ t -> (go[@tailcall]) (acc+1) t
    | _ -> failwith "Was not a numeral"
  in
  go 0

(** Precedence levels *)
let atom = P.nonassoc 11
let juxtaposition = P.left 10
let arrow = P.right 3

(** Determine the precedence level of the thing we are about to print *)
let classify_tm =
  function
  | Univ -> atom
  | Var _ -> atom
  | Pi _ -> arrow
  | Sigma _ -> arrow
  | Pair _ -> atom
  | Fst _ -> juxtaposition
  | Snd _ -> juxtaposition
  | Lam _ -> arrow
  | Ap _ -> juxtaposition
  | Nat -> atom
  | Zero -> atom
  | Succ n ->
      begin
        try let _ = to_numeral n in atom
        with Failure _ -> juxtaposition
      end
  | NatElim _ -> juxtaposition

(** Wrap in parens with a pretty printer *)
let pp_braced pp fmt a = Format.fprintf fmt "(%a)" pp a

(** Conditionally wrap in parens based upon [penv] (current precedence) versus
    what [classify] gives *)
let pp_braced_cond classify plain_pp penv fmt tm =
  let this = classify tm in
  if P.parens penv this then
    pp_braced (plain_pp this penv) fmt tm
  else
    plain_pp this penv fmt tm

(** Pretty print a term *)
let rec pp env =
  pp_braced_cond classify_tm @@ fun this _penv fmt ->
  function
  | Var i ->
    begin
      try Ident.pp fmt (Bwd.nth env i)
      with Failure _ ->
        Format.fprintf fmt "![bad index %d]!" i
    end
  | Pi (nm, a, b) -> Format.fprintf fmt "Π(%a : %a), %a" Ident.pp nm (pp env P.isolated) a (pp (env #< nm) (P.right_of this)) b
  | Sigma (nm, a, b) -> Format.fprintf fmt "Σ(%a : %a), %a" Ident.pp nm (pp env P.isolated) a (pp (env #< nm) (P.right_of this)) b
  | Pair (a, b) -> Format.fprintf fmt "(%a, %a)" (pp env P.isolated) a (pp env P.isolated) b
  | Fst a -> Format.fprintf fmt "fst %a" (pp env (P.right_of this)) a
  | Snd a -> Format.fprintf fmt "snd %a" (pp env (P.right_of this)) a
  | Lam (nm, t) -> Format.fprintf fmt "λ %a. %a" Ident.pp nm (pp (env #< nm) (P.right_of this)) t
  | Ap (f, a) -> Format.fprintf fmt "%a %a" (pp env (P.left_of this)) f (pp env (P.right_of this)) a
  | Nat -> Format.fprintf fmt "ℕ"
  | Zero -> Format.fprintf fmt "0"
  | (Succ n') as n ->
    begin
      try Format.fprintf fmt "%d" (to_numeral n)
      with Failure _ ->
        Format.fprintf fmt "succ %a" (pp env (P.right_of juxtaposition)) n'
    end
  | NatElim r -> Format.fprintf fmt "nat-elim %a %a %a %a"(pp env (P.right_of this)) r.mot (pp env (P.right_of this)) r.zero (pp env (P.right_of this)) r.succ (pp env (P.right_of this)) r.scrut
  | Univ -> Format.fprintf fmt "U"


let pp_toplevel = pp Emp P.isolated
