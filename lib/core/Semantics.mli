(** {1 Evaluation} This module defines the core evaluation algorithm, along with 
    eliminators for values. *)

module S := Syntax
module D := Domain

open TermBuilder

val eval : env:D.env -> S.t -> D.t
val eval_top : S.t -> D.t

val do_ap : D.t -> D.t -> D.t
val inst_clo : D.clo -> D.t -> D.t
val graft_value : S.t Graft.t -> D.t
