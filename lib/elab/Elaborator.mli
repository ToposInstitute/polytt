module CS := Syntax
module D := Core.Domain
module S := Core.Syntax

val chk : CS.t -> D.tp -> S.t
val syn : CS.t -> D.tp * S.t
