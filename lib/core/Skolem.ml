module Sem = Semantics

module D = Domain
module S = Syntax

exception NotConstant

let inst_const_clo ~env ~tp clo =
  let v = Sem.inst_clo clo (D.skolem tp) in
  try
    (* Equate a term with itself to flush out any skolems.
       Thanks Verity for the diabolical trick. *)
    Conversion.equate ~env ~tp:D.Univ v v;
    Some v
  with
  | Conversion.Unequal ->
    None
