open Bwd
open Bwd.Infix

module D = Domain
module S = Syntax

type 'a tb = int -> 'a

(** A {!type:'a tb} can be thought of a piece of syntax that is
    relative to some environment. *)
let run_tb (env : D.env) (k : 'a tb) : 'a =
  k (Bwd.length env)

(** Convert a DeBruijin level into a DeBruijin indexed variable relative to the environment. *)
let var (lvl : int) : S.t tb =
  fun size ->
  S.Var (size - lvl - 1)

let bind_var (k : int -> 'a tb) : 'a tb =
  fun size ->
  k size (size + 1)

let scope (k : S.t tb -> 'a tb) : 'a tb =
  bind_var (fun lvl -> k (var lvl))

module TB =
struct
  let pi ?(name = `Anon) base fam size =
    S.Pi(name, base size, scope fam size)

  let lam ?(name = `Anon) body size =
    S.Lam (name, scope body size)

  let ap fn arg size =
    S.Ap (fn size, arg size)

  let sigma ?(name = `Anon) base fam size =
    S.Sigma(name, base size, scope fam size)

  let fst tm size =
    S.Fst (tm size)

  let snd tm size =
    S.Snd (tm size)

  let nat _ =
    S.Nat

  let zero _ =
    S.Zero

  let succ n size =
    S.Succ (n size)

  let finset ls _ =
    S.FinSet ls

  let label ls l _ =
    S.Label (ls, l)

  let cases mot cases case size =
    S.Cases (mot size, cases size, case size)

  let univ _ =
    S.Univ

  let base p size =
    S.Base (p size)

  let fib p x size =
    S.Fib (p size, x size)

  let hom_base f base size =
    S.HomBase (f size, base size)

  let hom_fib f base fib size =
    S.HomFib (f size, base size, fib size)
end

module Graft =
struct
  type 'a t = D.env -> 'a tb * D.env

  let value (v : D.t) (k : S.t tb -> 'a t) : 'a t =
    fun env ->
    (* Create a variable that points to the end of the extended context.
       The DeBruijin arithmetic is a little tricky, but lets us avoid a subtraction. *)
    let x = var (Bwd.length env) in
    let env = env #< v in
    k x env

  let build (builder : 'a tb) : 'a t =
    fun env -> (builder, env)

  let graft (k : 'a t) : 'a * D.env =
    let (tb, env) = k Emp in
    (run_tb env tb , env)
end
