open Core

module S = Syntax
module D = Domain

module rec Chk : sig
  type tac
  val rule : (D.tp -> S.t) -> tac
  val run : tac -> D.tp -> S.t
end =
struct
  type tac = D.tp -> S.t
  let rule k = k
  let run k tp = k tp
end

and Syn : sig
  type tac
  val rule : (unit -> D.tp * S.t) -> tac
  val run : tac -> D.tp * S.t
end =
struct
  type tac = unit -> D.tp * S.t
  let rule k = k
  let run k = k ()
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
    Eff.abstract ~name tp @@ fun value ->
    k {tp; value}
end
