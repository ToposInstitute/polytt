(** {1 Evaluation} This module defines the core evaluation algorithm, along with
    eliminators for values. *)

module S := Syntax
module D := Domain

open Bwd
open TermBuilder

(** Given an environment context, convert from a Syntax term to a Domain term. *)
val eval : env:D.env -> S.t -> D.t

(** Entrypoint to the evaluator. Calls 'eval' with an empty environment. *)
val eval_top : S.t -> D.t

val do_ap : D.t -> D.t -> D.t
val do_aps : D.t -> D.t list -> D.t
val do_fst : D.t -> D.t
val do_snd : D.t -> D.t
val do_nat_elim : mot:D.t -> zero:D.t -> succ:D.t -> scrut:D.t -> D.t
val do_base : D.t -> D.t
val do_fib : D.t -> D.t -> D.t
val do_log : D.t -> D.t
val do_hom_elim : D.t -> D.t -> D.t
val do_spine : D.t -> D.frame bwd -> D.t

val inst_clo : D.tm_clo -> D.t -> D.t
val graft_value : S.t Graft.t -> D.t
