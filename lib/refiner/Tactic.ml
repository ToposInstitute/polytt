open Core
open Bwd
open Bwd.Infix
include Eff

open Ident

include TermBuilder

module rec Chk : sig
  type tac
  val rule : (D.tp -> S.t) -> tac
  val run : tac -> D.tp -> S.t
  val run2 : tac -> D.tp -> D.tp -> (S.t * bool)
  val syn : Syn.tac -> Chk.tac
  val locate : Asai.Span.t -> tac -> tac
end =
struct
  type tac = D.tp -> S.t
  let rule k = k
  let run k tp = k tp
  let run2 k tp1 tp2 = try k tp1, false with _ -> k tp2, true
  let syn tac =
    rule @@ fun goal ->
    let (actual, tm) = Syn.run tac in
    Coe.coe actual goal tm
  let locate loc k tp =
    Error.locate loc @@ fun () ->
    k tp
end

and Syn : sig
  type tac
  val rule : (unit -> D.tp * S.t) -> tac
  val run : tac -> D.tp * S.t
  val ann : Chk.tac -> Chk.tac -> tac
  val locate : Asai.Span.t -> tac -> tac
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
  let locate loc k () =
    Error.locate loc @@ fun () ->
    k ()
end

and Hom : sig
  type tac
  val rule : (D.t * (unit -> S.t) -> S.t) -> tac
  val run : tac -> D.t * (unit -> S.t) -> S.t
  val locate : Asai.Span.t -> tac -> tac
end =
struct
  type tac = D.t * (unit -> S.t) -> S.t
  let rule k = k
  let run k tp = k tp
  let locate loc k (tp, set) =
    Error.locate loc @@ fun () ->
    k (tp, set)
end

(* TODO: need a better model for this, see Prog.neg_lam *)
and Prog : sig
  type tac
  val rule : (unit -> unit) -> tac
  val run : tac -> unit -> unit
  val locate : Asai.Span.t -> tac -> tac
end =
struct
  type tac = unit -> unit
  let rule k = k
  let run k tp = k tp
  let locate loc k () =
    Error.locate loc @@ fun () ->
    k ()
end

and NegChk : sig
  type tac
  val rule : (D.t -> (D.t -> unit)) -> tac
  val run : tac -> D.t -> (D.t -> unit)
  val syn : NegSyn.tac -> tac
  val locate : Asai.Span.t -> tac -> tac
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
  let locate loc k tp =
    Error.locate loc @@ fun () ->
    k tp
end

and NegSyn : sig
  type tac
  val rule : (unit -> D.t * (D.t -> unit)) -> tac
  val run : tac -> D.t * (D.t -> unit)
  val locate : Asai.Span.t -> tac -> tac
end =
struct
  type tac = unit -> D.t * (D.t -> unit)
  let rule k = k
  let run k = k ()
  let locate loc k () =
    Error.locate loc @@ fun () ->
    k ()
end

and Var : sig
  type tac

  val value : tac -> D.t
  val name : tac -> Ident.t
  val tree : tac -> (D.tp * D.t) Ident.pat
  val syn : tac -> Syn.tac
  val abstract : ?name:Ident.binder -> D.tp -> (tac -> 'a) -> 'a
  val abstracts : ?names:Ident.binder list -> D.tp -> (tac list -> 'a) -> 'a
  val concrete : ?name:Ident.binder -> D.tp -> D.t -> (tac -> 'a) -> 'a
  val fresh_name : Ident.t -> Ident.t

  val choose : Ident.binder -> Ident.t
  val choose_many : Ident.binder list -> Ident.t list
end =
struct
  type tac = Ident.t * (D.tp * D.t) * (D.tp * D.t) Ident.pat

  let value (_, (_, v), _) = v
  let name (ident, _, _) = ident
  let tree (_, _, t) = t

  let syn (_, (tp, value), _) =
    Syn.rule @@ fun () ->
    let tm = Eff.quote ~tp value in
    tp, tm

  let fresh_name : Ident.t -> Ident.t = function
  | `Anon -> `Machine (Locals.size ())
  | name -> name

  let fresh_name_at : int -> Ident.t -> Ident.t =
  fun i -> function
  | `Anon -> `Machine i
  | name -> name

  let rec fresh_names_step : int ref -> Ident.binder -> Ident.binder =
  fun i -> function
  | Var ident ->
    let ident = fresh_name_at !i ident in
    i := !i+1;
    Var ident
  | Tuple (l, r) ->
    let l = fresh_names_step i l in
    let r = fresh_names_step i r in
    Tuple (l, r)

  let fresh_names : Ident.binder -> Ident.binder =
    fun b ->
      let i = ref (Locals.size ()) in
      fresh_names_step i b

  let choose = fun name -> fresh_name (Ident.choose name)

  let choose_many =
    let i = ref 0 in
    List.map @@ fun name ->
      Ident.choose (fresh_names_step i name)

  let abstracts ?(names = [Var `Anon]) tp k =
    (* TODO: fresh_name *)
    Locals.abstracts ~names tp @@ fun tacs ->
    k tacs

  let abstract ?(name = Var `Anon) tp k =
    Locals.abstract ~name:(fresh_names name) tp k

  let concrete ?(name = Var `Anon) tp value k =
    Locals.concrete ~name:(fresh_names name) tp value k
end

and NegVar : sig
  type tac
  val abstract : ?name:Ident.binder -> D.tp -> (tac -> 'a) -> 'a
  val borrow : tac -> D.t
  val name : tac -> Ident.t
  val tree : tac -> int Ident.pat
  val revert : D.t -> (unit -> unit) -> (D.t -> unit) option
end =
struct
  type tac = Ident.t * (D.tp * D.t) * int Ident.pat

  let abstract ?(name = Var `Anon) tp k =
    Locals.abstract_neg ~name tp k

  let borrow (_, (_, v), _) = v
  let name (ident, _, _) = ident
  let tree (_, _, t) = t

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
      (* Since this is the positive fragment, we do not need negatives here *)
      let tp = Quote.quote ~env:{ pos_size = size; neg_size = 0; neg = Emp } ~tp:D.Univ tp in
      Format.fprintf fmt "+ %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (S.abs_pos ppenv name) (size + 1)) ctx
  in
  go ppenv 0 fmt ctx

let pp_sequent_neg_ctx (ppenv : S.ppenv) fmt (ctx, k) =
  let pos_size = Bwd.length ppenv.pos in
  let rec go ppenv neg_size neg fmt ctx =
    match ctx with
    | [] ->
      k ppenv fmt
    | (name, (tp, (D.Neu (_, { hd = D.Borrow sz; spine = Emp }) as tm))) :: ctx when sz = neg_size ->
      let tp = Quote.quote ~env:{ pos_size; neg_size; neg } ~tp:D.Univ tp in
      Format.fprintf fmt "- %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (S.abs_neg ppenv name) (neg_size + 1) (neg #< tm)) ctx
    | (name, (tp, tm)) :: ctx when false ->
      let tp = Quote.quote ~env:{ pos_size; neg_size; neg } ~tp:D.Univ tp in
      Format.fprintf fmt "- %a ← … : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tp
        (go (S.abs_neg ppenv name) (neg_size + 1) (neg #< tm)) ctx
    | (name, (tp, tm)) :: ctx when false ->
      let tm_s = Quote.quote ~env:{ pos_size; neg_size; neg } ~tp tm in
      let tp = Quote.quote ~env:{ pos_size; neg_size; neg } ~tp:D.Univ tp in
      Format.fprintf fmt "- %a ← %a : %a@.%a"
        Ident.pp name
        (S.pp ppenv Precedence.isolated) tm_s
        (S.pp ppenv Precedence.isolated) tp
        (go (S.abs_neg ppenv name) (neg_size + 1) (neg #< tm)) ctx
    | (name, (_tp, tm)) :: ctx ->
      Format.fprintf fmt "%a"
        (go (S.abs_neg ppenv name) (neg_size + 1) (neg #< tm)) ctx
  in
  go ppenv 0 Emp fmt ctx

let pp_sequent_goal is_neg goal_tm goal_tp ppenv fmt =
  Format.fprintf fmt "──────────────@.%s ⊢ %a : %a@."
    (if is_neg then "-" else "+")
    (S.pp ppenv Precedence.isolated) goal_tm
    (S.pp ppenv Precedence.isolated) goal_tp

let pp_sequent_pos_goal = pp_sequent_goal false
let pp_sequent_neg_goal = pp_sequent_goal true

let pp_sequent_nogoal _ppenv fmt =
  Format.fprintf fmt "──────────────@."

let print_ctx fmt k =
  let ppenv = Locals.ppenv () in
  let ctx = Locals.local_types () in
  let neg_ctx = Bwd.combine (Locals.neg_types ()) (Locals.neg_values ()) in
  pp_sequent_ctx { pos = Emp; neg_size = 0; neg = Emp } fmt
    ( List.combine (Bwd.to_list ppenv.pos) (Bwd.to_list ctx)
    , fun halfway fmt ->
      pp_sequent_neg_ctx halfway fmt
        ( List.combine (Bwd.to_list ppenv.neg) (Bwd.to_list neg_ctx)
        , k
        )
    )
