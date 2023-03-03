open Asai
open Bwd
open Core
open Errors
open TermBuilder

module D := Domain
module S := Syntax

module Cell : sig
  type pos = { name : Ident.t; tp : D.tp; value : D.t; }
  type neg = { name : Ident.t; tp : D.tp; lvl : int }

  type t =
    | Pos of pos
    | Neg of neg

  val name : t -> Ident.t
end

module Linearity : sig
  val run : (unit -> 'a) -> 'a
  (** Marks a linear variable as being used, and returns [true]
      if it had already been used. *)

  val consume : Cell.neg -> bool
end

module Globals : sig
  type resolved =
    | Def of { tm : D.t; tp : D.tp }
  val resolve : Ident.path -> resolved option
  val run : resolve:(Yuujinchou.Trie.path -> resolved option) -> (unit -> 'a) -> 'a
end

module Locals : sig
  val run_top : (unit -> 'a) -> 'a
  val resolve : Ident.path -> Cell.pos option
  val resolve_neg : Ident.path -> Cell.neg option
  val concrete : ?name:Ident.t -> D.tp -> D.t -> (unit -> 'a) -> 'a
  val abstract : ?name:Ident.t -> D.tp -> (D.t -> 'a) -> 'a
  val local_types : unit -> D.tp bwd
  val ppenv : unit -> Ident.t bwd
  val size : unit -> int

  val abstract_neg : ?name:Ident.t -> D.tp -> (int -> 'a) -> 'a
end

module Error : sig
  val error : Code.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
  val locate : Span.t -> (unit -> 'a) -> 'a
  val run : loc:Span.t -> (unit -> 'a) -> 'a
end

module Hole : sig
  val run : (unit -> 'a) -> 'a
  val fresh : unit -> int
end

val quote : tp:D.tp -> D.t -> S.t
val equate : tp:D.tp -> D.t -> D.t -> unit
val eval : S.t -> D.t
val inst_const_clo : tp:D.t -> D.tm_clo -> D.t option
val inst_clo : D.tm_clo -> D.t -> D.t
val graft_value : S.t Graft.t -> D.t

val do_ap : D.t -> D.t -> D.t
val do_fst : D.t -> D.t
val do_snd : D.t -> D.t
val do_nat_elim : mot:D.t -> zero:D.t -> succ:D.t -> scrut:D.t -> D.t
val do_negate : D.t -> D.t
val do_base : D.t -> D.t
val do_fib : D.t -> D.t -> D.t

