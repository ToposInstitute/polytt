module D := Domain

(** Check that a closure denotes a constant function *)
val inst_const_clo : size:int -> cells:D.t list -> tp:D.tp -> D.tm_clo -> D.t option
