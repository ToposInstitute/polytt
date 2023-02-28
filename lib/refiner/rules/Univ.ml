open Tactic

let formation = Chk.rule @@
  function
  | D.Univ -> S.Univ (* type is in type. *)
  | _ -> failwith "FIXME: Better error handling"
