open Asai
open Core
open Errors
open TermBuilder

module D := Domain
module S := Syntax

module Cell : sig
  type t = {
    name : Ident.t;
    tp : D.tp;
    value : D.t;
  }
end

val run_top : loc:Span.t -> (unit -> 'a) -> 'a
val located : Span.t -> (unit -> 'a) -> 'a
val error : Code.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val quote : tp:D.tp -> D.t -> S.t
val equate : tp:D.tp -> D.t -> D.t -> unit
val eval : S.t -> D.t
val inst_clo : D.clo -> D.t -> D.t
val graft_value : S.t Graft.t -> D.t

val do_ap : D.t -> D.t -> D.t
val do_fst : D.t -> D.t
val do_snd : D.t -> D.t
val do_nat_elim : mot:D.t -> zero:D.t -> succ:D.t -> scrut:D.t -> D.t

val abstract : ?name:Ident.t -> D.tp -> (D.t -> 'a) -> 'a
val lookup_var : Ident.t -> Cell.t option
