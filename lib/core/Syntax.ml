(** The syntax of the core language.
    This module repackages definitions in Data.ml for nicer qualified imports. *)

open Bwd
open Bwd.Infix

module P = Precedence

type labelset = string list
type label = string
type 'a labeled = (string * 'a) list

type ppenv = { pos : Ident.t bwd; neg_size : int; neg : Ident.t bwd }

type t = Data.syn =
  | Var of int
  | Borrow of int
  | Pi of Ident.t * t * t
  | Lam of Ident.t * t
  | Let of Ident.t * t * t
  | Ap of t * t
  | Sigma of Ident.t * t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Eq of t * t * t
  | Refl of t
  | Nat
  | Zero
  | Succ of t
  | NatElim of { mot : t; zero : t; succ : t; scrut : t }
  | FinSet of labelset
  | Label of labelset * label
  | Cases of t * t labeled * t
  | Univ
  | Poly
  | PolyIntro of Ident.t * t * t
  | Base of t
  | Fib of t * t
  | Hom of t * t
  | HomLam of t
  | HomElim of t * t
  | Hole of t * int
  | Skolem of t

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

(** Raw printing for debugging *)
let rec dump fmt =
  function
  | Univ -> Format.fprintf fmt "univ"
  | Var i -> Format.fprintf fmt "S.var[%i]" i
  | Borrow i -> Format.fprintf fmt "S.borrow[%i]" i
  | Pi (nm, a, b) -> Format.fprintf fmt "pi[%a, %a, %a]" Ident.pp nm dump a dump b
  | Sigma (nm, a, b) -> Format.fprintf fmt "sigma[%a, %a, %a]" Ident.pp nm dump a dump b
  | Pair (a, b) -> Format.fprintf fmt "pair[%a, %a]" dump a dump b
  | Fst a -> Format.fprintf fmt "fst[%a]" dump a
  | Snd a -> Format.fprintf fmt "snd[%a]" dump a
  | Lam (nm, t) -> Format.fprintf fmt "lam[%a, %a]" Ident.pp nm dump t
  | Let (nm, t1, t2) -> Format.fprintf fmt "let[%a = %a in %a ]" Ident.pp nm dump t1 dump t2
  | Ap (f, a) -> Format.fprintf fmt "ap[%a, %a]" dump f dump a
  | Eq (t, a, b) -> Format.fprintf fmt "eq[%a, %a, %a]" dump t dump a dump b
  | Refl (a) -> Format.fprintf fmt "refl[%a]" dump a
  | Nat -> Format.fprintf fmt "nat"
  | Zero -> Format.fprintf fmt "zero"
  | Succ n -> Format.fprintf fmt "succ[%a]" dump n
  | NatElim r -> Format.fprintf fmt "nat-elim[%a, %a, %a, %a]" dump r.mot dump r.zero dump r.succ dump r.scrut
  | FinSet ls -> Format.fprintf fmt "finset[%a]" (pp_sep_list Format.pp_print_string) ls
  | Label (ls, l) -> Format.fprintf fmt "label[%a, %a]" (pp_sep_list Format.pp_print_string) ls Format.pp_print_string l
  | Cases (mot, cases, case) -> Format.fprintf fmt "cases[%a, %a, %a]" dump mot (pp_sep_list (fun fmt (l, v) -> Format.fprintf fmt "%a = %a" Format.pp_print_string l dump v)) cases dump case
  | Poly ->
    Format.fprintf fmt "poly"
  | PolyIntro (nm, base, fib) ->
    Format.fprintf fmt "poly-intro[%a, %a, %a]"
      Ident.pp nm
      dump base
      dump fib
  | Base p ->
    Format.fprintf fmt "base[%a]"
      dump p
  | Fib (p, i) ->
    Format.fprintf fmt "fib[%a, %a]"
      dump p
      dump i
  | Hom (p, q) ->
    Format.fprintf fmt "hom[%a, %a]"
      dump p
      dump q
  | HomLam wrapped ->
    Format.fprintf fmt "hom-lam[%a]"
      dump wrapped
  | HomElim (hom, i) ->
    Format.fprintf fmt "hom-elim[%a, %a]"
      dump hom
      dump i
  | Hole (tp, n) -> Format.fprintf fmt "hole[%a, %d]" dump tp n
  | Skolem _ -> Format.fprintf fmt "skolem"

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
let star = P.right 5
let hom = P.right 4
let arrow = P.right 3
let equals = P.right 2

(** Determine the precedence level of the thing we are about to print *)
let classify_tm =
  function
  | Univ -> atom
  | Poly -> atom
  | Var _ -> atom
  | Borrow _ -> juxtaposition
  | Pi _ -> arrow
  | Sigma (`Anon, _, _) -> star
  | Sigma _ -> arrow
  | Pair _ -> atom
  | PolyIntro _ -> star
  | Fst _ -> juxtaposition
  | Snd _ -> juxtaposition
  | Base _ -> juxtaposition
  | Fib _ -> juxtaposition
  | Lam _ -> arrow
  | Let _ -> atom
  | Ap _ -> juxtaposition
  | Eq _ -> equals
  | Refl _ -> juxtaposition
  | Nat -> atom
  | Zero -> atom
  | Succ n ->
    begin
      try let _ = to_numeral n in atom
      with Failure _ -> juxtaposition
    end
  | NatElim _ -> juxtaposition
  | FinSet _ -> atom
  | Label _ -> atom
  | Cases _ -> juxtaposition
  | Hom _ -> hom
  | HomLam _ -> arrow
  | HomElim _ -> juxtaposition
  | Hole _ -> atom
  | Skolem _ -> atom

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

let abs_pos env name = { env with pos = env.pos #< name }

let rec collect_lams env nms tm =
  match tm with
  | Lam (nm, t) ->
    collect_lams (abs_pos env nm) (nm :: nms) t
  | body -> env, List.rev nms, body

(** Pretty print a term *)
let rec pp (env : ppenv) =
  pp_braced_cond classify_tm @@ fun this _penv fmt ->
  function
  | Var i ->
    begin
      try Ident.pp fmt (Bwd.nth env.pos i)
      with Failure _ ->
        Format.fprintf fmt "![bad var index %d]!" i
    end
  | Borrow i ->
    begin
      try Ident.pp fmt (Bwd.nth env.neg ((env.neg_size - 1) - i))
      with Failure _ ->
        Format.fprintf fmt "![bad borrow index %d]!" i
    end
  | Pi (`Anon, a, b) ->
    Format.fprintf fmt "%a → %a"
      (pp env (P.left_of this)) a
      (pp (abs_pos env `Anon) (P.right_of this)) b
  | Pi (nm, a, b) ->
    Format.fprintf fmt "(%a : %a) → %a"
      Ident.pp nm
      (pp env P.isolated) a
      (pp (abs_pos env nm) (P.right_of this)) b
  | Sigma (`Anon, a, b) ->
    Format.fprintf fmt "%a × %a"
      (pp env (P.left_of this)) a
      (pp (abs_pos env `Anon) (P.right_of this)) b
  | Sigma (nm, a, b) ->
    Format.fprintf fmt "(%a : %a) × %a"
      Ident.pp nm
      (pp env P.isolated) a
      (pp (abs_pos env nm) (P.right_of this)) b
  | Pair (a, b) ->
    Format.fprintf fmt "(%a , %a)"
      (pp env P.isolated) a
      (pp env P.isolated) b
  | Fst a ->
    Format.fprintf fmt "fst %a"
      (pp env (P.right_of this)) a
  | Snd a ->
    Format.fprintf fmt "snd %a"
      (pp env (P.right_of this)) a
  | Lam (nm, t) ->
    let (env , nms, body) = collect_lams env [] (Lam (nm, t)) in
    Format.fprintf fmt "λ %a → %a"
      (pp_sep_list ~sep:" " Ident.pp) nms
      (pp env (P.right_of this)) body
  | Let (nm, t1, t2) ->
    Format.fprintf fmt "let %a = %a in %a"
      Ident.pp nm
      (pp env (P.right_of this)) t1
      (pp (abs_pos env nm) (P.right_of this)) t2
  | Ap (f, a) ->
    Format.fprintf fmt "%a %a"
      (pp env (P.left_of this)) f
      (pp env (P.right_of this)) a
  | Eq (_, a, b) ->
    Format.fprintf fmt "%a = %a"
      (pp env (P.left_of this)) a
      (pp env (P.right_of this)) b
  | Refl (a) ->
    Format.fprintf fmt "refl %a"
      (pp env (P.right_of this)) a
  | Nat ->
    Format.fprintf fmt "ℕ"
  | Zero ->
    Format.fprintf fmt "0"
  | (Succ n') as n ->
    begin
      try Format.fprintf fmt "%d" (to_numeral n)
      with Failure _ ->
        Format.fprintf fmt "succ %a" (pp env (P.right_of juxtaposition)) n'
    end
  | NatElim r ->
    Format.fprintf fmt "nat-elim %a %a %a %a"
      (pp env (P.right_of this)) r.mot
      (pp env (P.right_of this)) r.zero
      (pp env (P.right_of this)) r.succ
      (pp env (P.right_of this)) r.scrut
  | Univ ->
    Format.fprintf fmt "Type"
  | FinSet [] ->
    Format.fprintf fmt "#{}"
  | FinSet ls ->
    Format.fprintf fmt "#{ %a }"
      (pp_sep_list (fun fmt l -> Format.pp_print_string fmt ("." ^ l))) ls
  | Label (_ls, l) ->
    Format.fprintf fmt ".%a"
      Format.pp_print_string l
  | Cases (_, [], case) ->
    Format.fprintf fmt "{} %a"
      (pp env (P.right_of this)) case
  | Cases (_, cases, case) ->
    Format.fprintf fmt "{ %a } %a"
      (pp_sep_list (fun fmt (l, v) -> Format.fprintf fmt ".%a = %a" Format.pp_print_string l (pp env P.isolated) v)) cases
      (pp env (P.right_of this)) case
  | Poly ->
    Format.fprintf fmt "Poly"
  | PolyIntro (nm, base, fib) ->
    Format.fprintf fmt "(%a : %a) × %a"
      Ident.pp nm
      (pp env P.isolated) base
      (pp (abs_pos env nm) P.isolated) fib
  | Base p ->
    Format.fprintf fmt "base %a"
      (pp env (P.right_of juxtaposition)) p
  | Fib (p, fib) ->
    Format.fprintf fmt "fib %a %a"
      (pp env (P.right_of juxtaposition)) p
      (pp env (P.right_of juxtaposition)) fib
  | Hom (p, q) ->
    Format.fprintf fmt "%a ⇒ %a"
      (pp env (P.left_of arrow)) p
      (pp env (P.right_of arrow)) q
  | HomLam wrapped ->
    Format.fprintf fmt "λ ~> FIXME %a FIXME" (pp env P.isolated) wrapped
  (* (pp_hom (abs_pos env p_name #< q_name) (P.right_of arrow)) bdy *)
  | HomElim (hom, i) ->
    Format.fprintf fmt "%a %a"
      (pp env (P.left_of juxtaposition)) hom
      (pp env (P.right_of juxtaposition)) i
  | Hole (_tp, n) -> Format.fprintf fmt "?%d" n
  | Skolem _ -> Format.fprintf fmt "skolem"

let pp_toplevel = pp { pos = Emp; neg_size = 0; neg = Emp } P.isolated
