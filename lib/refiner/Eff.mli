open Core
module D := Domain
module S := Syntax

val quote : tp:D.tp -> D.t -> S.t
val eval : S.t -> D.t
val inst_clo : D.clo -> D.t -> D.t

val abstract : ?name:Ident.t -> D.tp -> (D.t -> 'a) -> 'a
