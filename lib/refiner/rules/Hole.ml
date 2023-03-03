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
    | (name, tp) :: ctx ->
      (* FIXME this does not include negatives *)
      let tp = Quote.quote ~size ~tp:D.Univ tp in
      Format.fprintf fmt "  %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (ppenv #< name) (size + 1)) (ctx, goal)
  in
  go ppenv 0 fmt (ctx, goal)

let unleash = Chk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  let ppenv = Locals.ppenv () in
  let ctx = Locals.local_types () in
  Format.printf "Encountered Hole!@.%a@."
    (* FIXME this does not include negatives *)
    (pp_sequent Emp) (List.combine (Bwd.to_list ppenv) (Bwd.to_list ctx), tp);

  S.Hole (tp, Hole.fresh ())
