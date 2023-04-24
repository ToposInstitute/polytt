module D := Domain
module Env := QuoteEnv

(** Check that a closure denotes a constant function *)
val inst_const_clo : env:Env.t -> tp:D.tp -> D.tm_clo -> D.t option
