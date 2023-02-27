module S := Syntax
module D := Domain

val eval : env:D.env -> S.t -> D.t
val eval_top : S.t -> D.t

val do_ap : D.t -> D.t -> D.t
val inst_clo : D.clo -> D.t -> D.t
