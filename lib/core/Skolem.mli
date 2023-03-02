module D := Domain

(** Check that a closure denotes a constant function *)
val inst_const_clo : D.tm_clo -> D.t option
