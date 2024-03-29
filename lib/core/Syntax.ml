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
  | (* t *)
    Var of int
  | (* t *)
    Global of Global.t
  | (* borrow t *)
    Borrow of int
  | (* Π (a : A), (B a) *)
    Pi of Ident.t * t * t
  | (* λ x. e *)
    Lam of Ident.t * t
  | (* let x = e in t *)
    Let of Ident.t * t * t
  | (* f a *)
    Ap of t * t
  | (* Σ (x : A), B x *)
    Sigma of Ident.t * t * t
  | (* (a , b) *)
    Pair of t * t
  | (* fst x *)
    Fst of t
  | (* snd x *)
    Snd of t
  | (* a = b *)
    Eq of t * t * t
  | (* refl *)
    Refl of t
  | (* ℕ *)
    Nat
  | (* zero *)
    Zero
  | (* succ n *)
    Succ of t
  | (* elim mot z s scrut *)
    NatElim of { mot : t; zero : t; succ : t; scrut : t }
  | (* #{ foo, bar } *)
    FinSet of labelset
  | (* .foo *)
    Label of labelset * label
  | (* { foo = syn₁, bar = syn₂ } e *)
    Cases of t * t labeled * t
  | (* Type *)
    Univ
  | (* Poly *)
    Poly
  | (* (p : P) × q *)
    PolyIntro of Ident.t * t * t
  | (* Repr *)
    Repr
  | (* y^(p) *)
    ReprIntro of t
  | (* base p *)
    Base of t
  | (* fib x y *)
    Fib of t * t
  | (* log r *)
    Log of t
  | ElRepr of t
  | (* p ⇒ q *)
    Hom of t * t
  | (* λ a⁺ a⁻ ⇒ p *)
    HomLam of t
  | (* x y *)
    HomElim of t * t
  | (* ? *)
    Hole of t * int
  | (* skolem *)
    Skolem of t

let rec shift_from j =
  function
  | Var i -> Var (if i >= j then i+1 else i)
  | Pi (nm, a, b) -> Pi (nm, shift_from j a, shift_from (j+1) b)
  | Sigma (nm, a, b) -> Sigma (nm, shift_from j a, shift_from (j+1) b)
  | Pair (a, b) -> Pair (shift_from j a, shift_from j b)
  | Fst a -> Fst (shift_from j a)
  | Snd a -> Snd (shift_from j a)
  | Lam (nm, t) -> Lam (nm, shift_from (j+1) t)
  | Let (nm, t1, t2) -> Let (nm, shift_from j t1, shift_from (j+1) t2)
  | Ap (f, a) -> Ap (shift_from j f, shift_from j a)
  | Eq (t, a, b) -> Eq (shift_from j t, shift_from j a, shift_from j b)
  | Refl a -> Refl (shift_from j a)
  | Succ n -> Succ (shift_from j n)
  | NatElim { mot; zero; succ; scrut } -> NatElim { mot = shift_from j mot; zero = shift_from j zero; succ = shift_from j succ; scrut = shift_from j scrut }
  | Cases (mot, cases, case) -> Cases (shift_from j mot, List.map (fun (l, e) -> l, shift_from j e) cases, shift_from j case)
  | PolyIntro (nm, base, fib) -> PolyIntro (nm, shift_from j base, shift_from (j+1) fib)
  | ReprIntro exp -> ReprIntro (shift_from j exp)
  | Base p -> Base (shift_from j p)
  | Fib (p, i) -> Fib (shift_from j p, shift_from j i)
  | Log r -> Log (shift_from j r)
  | Hom (p, q) -> Hom (shift_from j p, shift_from j q)
  | HomLam wrapped -> HomLam (shift_from j wrapped)
  | HomElim (hom, i) -> HomElim (shift_from j hom, shift_from j i)
  | Hole (tp, n) -> Hole (shift_from j tp, n)
  | Skolem tp -> Skolem (shift_from j tp)
  | e -> e

let shift = shift_from 0

let pp_sep_list ?(sep = ", ") pp_elem fmt xs =
  Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt sep) pp_elem fmt xs

(** Raw printing for debugging *)
let rec dump fmt =
  function
  | Univ -> Format.fprintf fmt "univ"
  | Var i -> Format.fprintf fmt "S.var[%i]" i
  | Global x -> Format.fprintf fmt "S.global[%a]" Global.dump x
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
  | Repr ->
    Format.fprintf fmt "repr"
  | ReprIntro exp ->
    Format.fprintf fmt "repr-intro[%a]"
      dump exp
  | Base p ->
    Format.fprintf fmt "base[%a]"
      dump p
  | Fib (p, i) ->
    Format.fprintf fmt "fib[%a, %a]"
      dump p
      dump i
  | Log r ->
    Format.fprintf fmt "log[%a]"
      dump r
  | ElRepr r ->
    Format.fprintf fmt "el-repr[%a]"
      dump r
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
  | Repr -> atom
  | Var _ -> atom
  | Global _ -> atom
  | Borrow _ -> juxtaposition
  | Pi _ -> arrow
  | Sigma (`Anon, _, _) -> star
  | Sigma _ -> arrow
  | Pair _ -> atom
  | PolyIntro _ -> star
  | ReprIntro _ -> atom
  | Fst _ -> juxtaposition
  | Snd _ -> juxtaposition
  | Base _ -> juxtaposition
  | Fib _ -> juxtaposition
  | Log _ -> juxtaposition
  | ElRepr _ -> juxtaposition
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

let abs_neg env name = { env with neg = env.neg #< name; neg_size = env.neg_size + 1 }

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
  | Global x ->
    Global.pp fmt x
  | Borrow i ->
    begin
      try Format.fprintf fmt "borrow %a" Ident.pp (Bwd.nth env.neg ((env.neg_size - 1) - i))
      with Failure _ ->
        Format.fprintf fmt "![bad borrow index %d]!" i
    end
  | Pi (`Anon, a, b) ->
    Format.fprintf fmt "%a → %a"
      (pp env (P.left_of this)) a
      (pp (abs_pos env `Anon) (P.right_of this)) b
  | Pi (nm, a, b) ->
    Format.fprintf fmt "Π (%a : %a), %a"
      Ident.pp nm
      (pp env P.isolated) a
      (pp (abs_pos env nm) (P.right_of this)) b
  | Sigma (`Anon, a, b) ->
    Format.fprintf fmt "%a × %a"
      (pp env (P.left_of this)) a
      (pp (abs_pos env `Anon) (P.right_of this)) b
  | Sigma (nm, a, b) ->
    Format.fprintf fmt "Σ (%a : %a), %a"
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
    Format.fprintf fmt "let %a := %a in %a"
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
    Format.fprintf fmt "Σ (%a : %a), %a"
      Ident.pp nm
      (pp env P.isolated) base
      (pp (abs_pos env nm) P.isolated) fib
  | Repr ->
    Format.fprintf fmt "Repr"
  | ReprIntro exp ->
    Format.fprintf fmt "y^%a"
      (* FIXME precedence? *)
      (pp env (P.surrounded_by atom)) exp
  | Base p ->
    Format.fprintf fmt "base %a"
      (pp env (P.right_of juxtaposition)) p
  | Fib (p, fib) ->
    Format.fprintf fmt "fib %a %a"
      (pp env (P.right_of juxtaposition)) p
      (pp env (P.right_of juxtaposition)) fib
  | Log r ->
    Format.fprintf fmt "log %a"
      (pp env (P.right_of juxtaposition)) r
  | ElRepr r ->
    Format.fprintf fmt "(%a : Poly)"
      (* FIXME precedence *)
      (pp env (P.right_of juxtaposition)) r
  | Hom (p, q) ->
    Format.fprintf fmt "%a ⇒ %a"
      (pp env (P.left_of arrow)) p
      (pp env (P.right_of arrow)) q
  | HomLam wrapped ->
    Format.fprintf fmt "%a" (pp env P.isolated) wrapped
  (* (pp_hom (abs_pos env p_name #< q_name) (P.right_of arrow)) bdy *)
  | HomElim (hom, i) ->
    Format.fprintf fmt "%a %a"
      (pp env (P.left_of juxtaposition)) hom
      (pp env (P.right_of juxtaposition)) i
  | Hole (_tp, n) -> Format.fprintf fmt "?%d" n
  | Skolem _ -> Format.fprintf fmt "skolem"

let pp_toplevel = pp { pos = Emp; neg_size = 0; neg = Emp } P.isolated
