(** {1 Conversion Checker} This module defines the conversion check algorithm. *)

module S := Syntax
module D := Domain

exception Unequal

val equate : size:int -> cells:D.t list -> tp:D.tp -> D.t -> D.t -> unit
