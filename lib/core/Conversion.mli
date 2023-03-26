(** {1 Conversion Checker} This module defines the conversion check algorithm. *)

module S := Syntax
module D := Domain
module Env := QuoteEnv

exception Unequal

val equate : env:Env.t -> tp:D.tp -> D.t -> D.t -> unit
