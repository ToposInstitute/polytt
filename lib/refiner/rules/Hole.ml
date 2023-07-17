open Core
open Tactic

module S = Syntax

let unleash = Chk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  Format.printf "Encountered hole with known type!@.%a@."
    (* FIXME this does not include negatives *)
    print_ctx (pp_sequent_goal tp);

  S.Hole (tp, Hole.fresh ())

let unleash_syn =
  Syn.rule @@ fun () ->
  let tp = Hole.fresh () in
  let tp_d = D.hole D.Univ tp in
  let tp_s = S.Hole (S.Univ, tp) in
  Format.printf "Encountered hole with unknown type!@.%a@."
    (* FIXME this does not include negatives *)
    print_ctx (pp_sequent_goal tp_s);

  tp_d , S.Hole (tp_s, Hole.fresh ())

let unleash_neg = NegChk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  Format.printf "Encountered negative hole with known type!@.%a@."
    (* FIXME this does not include negatives *)
    print_ctx (pp_sequent_goal tp);
  (* TODO do we need stuff here? *)
  fun _ -> ()

let unleash_neg_syn =
  NegSyn.rule @@ fun () ->
  let tp = Hole.fresh () in
  let tp_d = D.hole D.Univ tp in
  let tp_s = S.Hole (S.Univ, tp) in
  Format.printf "Encountered negative hole with unknown type!@.%a@."
    (* FIXME this does not include negatives *)
    print_ctx (pp_sequent_goal tp_s);
  (* TODO do we need stuff here? *)
  tp_d , fun _ -> ()
