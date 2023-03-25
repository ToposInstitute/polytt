(** {1 Quoting} This module defines the quoting algorithm, which transforms
    values into syntax. This is where η-expansion occurs, along with evaluation
    under binders. *)

module S := Syntax
module D := Domain

val quote : size:int -> cells:D.t list -> tp:D.t -> D.t -> S.t
val quote_top : tp:D.t -> D.t -> S.t
