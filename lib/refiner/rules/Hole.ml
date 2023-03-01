open Bwd
open Bwd.Infix
open Core
open Errors
open Tactic

module S = Syntax  

let pp_sequent ppenv fmt (ctx, goal) =
  let rec go ppenv size fmt (ctx, goal) =
    match ctx with
    | [] ->
      Format.fprintf fmt "──────────────@.  ⊢ %a@."
        (S.pp ppenv Precedence.isolated) goal
    | cell :: ctx ->
      let tp = Quote.quote ~size ~tp:D.Univ (Cell.tp cell) in
      let nm = Cell.name cell in
      Format.fprintf fmt "  %a : %a@.%a"
        Ident.pp nm
        (S.pp ppenv Precedence.isolated) tp
        (go (ppenv #< nm) (size + 1)) (ctx, goal)
  in
  go ppenv (Locals.size ()) fmt (ctx, goal)

let unleash = Chk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  let ppenv = Locals.ppenv () in
  let ctx = Locals.locals () in
  Format.printf "Encountered Hole!@.%a@."
    (pp_sequent ppenv) (ctx, tp);

  S.Hole (tp, Hole.fresh ())
