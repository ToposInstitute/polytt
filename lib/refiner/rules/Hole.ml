open Core
open Tactic

module S = Syntax

let unleash = Chk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  let tm = S.Hole (tp, Hole.fresh ()) in
  Format.printf "Encountered hole with known type!@.%a@."
    print_ctx (pp_sequent_pos_goal tm tp);
  tm

let unleash_syn =
  Syn.rule @@ fun () ->
  let tp = Hole.fresh () in
  let tp_d = D.hole D.Univ tp in
  let tp_s = S.Hole (S.Univ, tp) in
  let tm = S.Hole (tp_s, Hole.fresh ()) in
  Format.printf "Encountered hole with unknown type!@.%a@."
    print_ctx (pp_sequent_pos_goal tm tp_s);

  tp_d , tm

let unleash_neg = NegChk.rule @@
  fun x ->
  let tp = quote ~tp:D.Univ x in
  Format.printf "Encountered negative hole with known type!@.%a@."
    print_ctx (pp_sequent_neg_goal (S.Hole (tp, Hole.fresh ())) tp);
  (* TODO do we need stuff here? *)
  fun _ -> ()

let unleash_neg_syn =
  NegSyn.rule @@ fun () ->
  let tp = Hole.fresh () in
  let tp_d = D.hole D.Univ tp in
  let tp_s = S.Hole (S.Univ, tp) in
  Format.printf "Encountered negative hole with unknown type!@.%a@."
    print_ctx (pp_sequent_neg_goal (S.Hole (tp_s, Hole.fresh ())) tp_s);
  (* TODO do we need stuff here? *)
  tp_d , fun _ -> ()

let unleash_prog =
  Prog.rule @@ fun () ->
  Format.printf "Here is the context!@.%a@."
    print_ctx pp_sequent_nogoal;
  ()

let unleash_hom =
  Hom.rule @@ fun (r, _tail) ->
  let tp_bd = do_base r in
  let tp_bs = quote ~tp:D.Univ tp_bd in
  let tm = Hole.fresh () in
  let tm_bd = D.hole tp_bd tm in
  let tm_bs = S.Hole (tp_bs, tm) in

  let tp_fd = do_fib r tm_bd in
  let tp_fs = quote ~tp:D.Univ tp_fd in
  let tm_fs = S.Hole (tp_fs, Hole.fresh ()) in

  Format.printf "Encountered hole at end of hom!@.%a@."
    print_ctx (fun ppenv fmt ->
      Format.fprintf fmt "──────────────@.+ ⊢ %a : %a@.- ⊢ %a : %a@."
      (S.pp ppenv Precedence.isolated) tm_bs
      (S.pp ppenv Precedence.isolated) tp_bs
      (S.pp ppenv Precedence.isolated) tm_fs
      (S.pp ppenv Precedence.isolated) tp_fs
      );
  S.Pair (tm_bs, S.Lam (`Anon, tm_fs))
