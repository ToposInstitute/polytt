open Core
open Bwd
open Bwd.Infix
include Eff

include TermBuilder

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
  val ann : Chk.tac -> Chk.tac -> tac
end =
struct
  type tac = unit -> D.tp * S.t
  let rule k = k
  let run k = k ()
  let ann chk tp_tac =
    rule @@ fun () ->
    let tp = Chk.run tp_tac D.Univ in
    let tp = eval tp in
    tp, Chk.run chk tp
end

and Hom : sig
  type tac
  val rule : (D.tp * (unit -> S.t) -> S.t) -> tac
  val run : tac -> D.tp * (unit -> S.t) -> S.t
end =
struct
  type tac = D.tp * (unit -> S.t) -> S.t
  let rule k = k
  let run k tp = k tp
end

and NegChk : sig
  type tac
  val rule : (D.t -> (D.t -> unit)) -> tac
  val run : tac -> D.t -> (D.t -> unit)
  val syn : NegSyn.tac -> tac
end =
struct
  type tac = D.t -> (D.t -> unit)
  let rule k = k
  let run k tp = k tp
  let syn tac =
    NegChk.rule @@ fun expected ->
    let (actual, tm) = NegSyn.run tac in
    equate ~tp:D.Univ expected actual;
    tm
end

and NegSyn : sig
  type tac
  val rule : (unit -> D.t * (D.t -> unit)) -> tac
  val run : tac -> D.t * (D.t -> unit)
end =
struct
  type tac = unit -> D.t * (D.t -> unit)
  let rule k = k
  let run k = k ()
end

and Var : sig
  type tac

  val value : tac -> D.t
  val syn : tac -> Syn.tac
  val abstract : ?name:Ident.t -> D.tp -> (tac -> 'a) -> 'a
  val concrete : ?name:Ident.t -> D.tp -> D.t -> (tac -> 'a) -> 'a
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

  let concrete ?(name = `Anon) tp value k =
    Eff.Locals.concrete ~name tp value @@ fun () ->
    k {tp; value}
end

and NegVar : sig
  type tac
  val abstract : ?name:Ident.t -> D.tp -> (tac -> 'a) -> 'a
  val concrete : ?name:Ident.t -> D.tp -> D.t -> (tac -> 'a) -> 'a
  val borrow : tac -> D.t
end =
struct
  type tac = { tp : D.tp; lvl : int }
  let abstract ?(name = `Anon) tp k =
    Locals.abstract_neg ~name tp @@ fun lvl ->
    k { tp; lvl }

  let concrete ?(name = `Anon) tp value k =
    Locals.abstract_neg ~name tp @@ fun lvl ->
    match Locals.consume_neg lvl () with
    | None -> invalid_arg ""
    | Some writer ->
      writer value;
      k { tp; lvl }

  let borrow { tp; lvl } = D.Neu (tp, { hd = D.Borrow lvl; spine = Emp })
end

let match_goal k =
  Chk.rule @@ fun goal ->
  Chk.run (k goal) goal

let match_syn tac k =
  Syn.rule @@ fun () ->
  let tp, tm = Syn.run tac in
  Syn.run @@ k (Syn.rule @@ fun () -> tp, tm) tp

let pp_sequent_ctx ppenv fmt (ctx, k) =
  let rec go ppenv size fmt ctx =
    match ctx with
    | [] ->
      k ppenv fmt
    | (name, tp) :: ctx ->
      (* FIXME this does not include negatives *)
      let tp = Quote.quote ~env:{ pos_size = size; neg_size = 0; neg = Emp } ~tp:D.Univ tp in
      Format.fprintf fmt "  %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (S.abs_pos ppenv name) (size + 1)) ctx
  in
  go ppenv 0 fmt ctx

let pp_sequent_goal goal ppenv fmt =
  Format.fprintf fmt "──────────────@.  ⊢ %a@."
    (S.pp ppenv Precedence.isolated) goal

let pp_sequent_nogoal _ppenv fmt =
  Format.fprintf fmt "──────────────@.  ⊢ ?@."

let print_ctx fmt k =
  let ppenv = Locals.ppenv () in
  let ctx = Locals.local_types () in
  pp_sequent_ctx { pos = Emp; neg_size = 0; neg = Emp } fmt (List.combine (Bwd.to_list ppenv.pos) (Bwd.to_list ctx), k)
