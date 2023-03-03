open Bwd
open Bwd.Infix
open Core
open Errors
open Tactic

module S = Syntax

let pp_sequent_ctx ppenv fmt (ctx, k) =
  let rec go ppenv size fmt ctx =
    match ctx with
    | [] ->
      k ppenv fmt
    | (name, tp) :: ctx ->
      (* FIXME this does not include negatives *)
      let tp = Quote.quote ~size ~tp:D.Univ tp in
      Format.fprintf fmt "  %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (ppenv #< name) (size + 1)) ctx
  in
  go ppenv 0 fmt ctx

let pp_sequent_goal goal ppenv fmt =
  Format.fprintf fmt "──────────────@.  ⊢ %a@."
    (S.pp ppenv Precedence.isolated) goal

let pp_sequent_nogoal _ppenv fmt =
  Format.fprintf fmt "──────────────@.  ⊢ ?@."

let unleash = Chk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  let ppenv = Locals.ppenv () in
  let ctx = Locals.local_types () in
  Format.printf "Encountered hole with known type!@.%a@."
    (* FIXME this does not include negatives *)
    (pp_sequent_ctx Emp) (List.combine (Bwd.to_list ppenv) (Bwd.to_list ctx), pp_sequent_goal tp);

  S.Hole (tp, Hole.fresh ())

let unleash_syn =
  Syn.rule @@ fun () ->
  let ppenv = Locals.ppenv () in
  let ctx = Locals.local_types () in
  let tp = Hole.fresh () in
  let tp_d = D.hole D.Univ tp in
  let tp_s = S.Hole (S.Univ, tp) in
  Format.printf "Encountered hole with unknown type!@.%a@."
    (* FIXME this does not include negatives *)
    (pp_sequent_ctx Emp) (List.combine (Bwd.to_list ppenv) (Bwd.to_list ctx), pp_sequent_goal tp_s);

  tp_d , S.Hole (tp_s, Hole.fresh ())
