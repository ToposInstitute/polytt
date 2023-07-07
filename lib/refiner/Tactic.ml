open Core
open Bwd
include Eff

open Ident

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

(* TODO: need a better model for this, see Prog.neg_lam *)
and Prog : sig
  type tac
  val rule : (unit -> unit) -> tac
  val run : tac -> unit -> unit
end =
struct
  type tac = unit -> unit
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
  val abstract : ?name:Ident.binder -> D.tp -> (tac -> 'a) -> 'a
  val abstracts : ?names:Ident.binder list -> D.tp -> (tac list -> 'a) -> 'a
  val concrete : ?name:Ident.binder -> D.tp -> D.t -> (tac -> 'a) -> 'a
end =
struct
  type tac = { tp : D.tp; value : D.t }

  let value tac = tac.value
  let syn {tp; value} =
    Syn.rule @@ fun () ->
    let tm = Eff.quote ~tp value in
    tp, tm

  let fresh_name : Ident.t -> Ident.t = function
  | `Anon -> `Machine (Locals.size ())
  | name -> name

  let rec fresh_names_step : (int * Ident.binder) -> (int * Ident.binder) =
  function
  | (i, Var ident) -> (i+1, Var (fresh_name ident))
  | (i, Tuple (l, r)) ->
      let (i, l) = fresh_names_step (i, l) in
      let (i, r) = fresh_names_step (i, r) in
      (i, Tuple (l, r))

  let fresh_names : Ident.binder -> Ident.binder =
    fun b -> snd (fresh_names_step (Locals.size (), b))

  let abstracts ?(names = [Var `Anon]) tp k =
    (* TODO: fresh_name *)
    Locals.abstracts ~names tp @@ fun values ->
    let tacs =
      values
      |> List.map @@ fun value -> { tp; value }
    in
    k tacs

  let abstract ?(name = Var `Anon) tp k =
    Locals.abstract ~name:(fresh_names name) tp @@ fun value ->
    k {tp; value}

  let concrete ?(name = Var `Anon) tp value k =
    Locals.concrete ~name:(fresh_names name) tp value @@ fun () ->
    k {tp; value}
end

and NegVar : sig
  type tac
  val abstract : ?name:Ident.binder -> D.tp -> (tac -> 'a) -> 'a
  val borrow : tac -> D.t
  val revert : D.t -> (unit -> unit) -> (D.t -> unit) option
end =
struct
  type tac = D.t
  let abstract ?(name = Var `Anon) tp k =
    Locals.abstract_neg ~name tp k

  let borrow x = x

  let revert =
    Eff.Locals.revert
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
