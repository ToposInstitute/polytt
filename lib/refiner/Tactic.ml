open Core
include Eff

module S = Syntax
module D = Domain

module rec Chk : sig
  type tac
  val rule : (D.tp -> S.t) -> tac
  val run : tac -> D.tp -> S.t
  val syn : Syn.tac -> Chk.tac
end =
struct
  type tac = D.tp -> S.t
  let rule k = k
  let run k tp = k tp
  let syn tac =
    rule @@ fun goal ->
    let (actual, tm) = Syn.run tac in
    equate ~tp:D.Univ goal actual;
    tm
end

and Syn : sig
  type tac
  val rule : (unit -> D.tp * S.t) -> tac
  val run : tac -> D.tp * S.t
  val ann : Chk.tac -> D.tp -> tac
end =
struct
  type tac = unit -> D.tp * S.t
  let rule k = k
  let run k = k ()
  let ann chk tp =
    rule @@ fun () ->
    tp, Chk.run chk tp
end

and Var : sig
  type tac

  val value : tac -> D.t
  val syn : tac -> Syn.tac
  val abstract : ?name:Ident.t -> D.tp -> (tac -> 'a) -> 'a
end =
struct
  type tac = { tp : D.tp; value : D.t }

  let value tac = tac.value
  let syn {tp; value} =
    Syn.rule @@ fun () ->
    let tm = Eff.quote ~tp value in
    tp, tm

  let abstract ?(name = `Anon) tp k =
    Locals.abstract ~name tp @@ fun value ->
    k {tp; value}
end
