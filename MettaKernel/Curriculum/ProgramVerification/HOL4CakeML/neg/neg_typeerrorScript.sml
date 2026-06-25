(* NEGATIVE: a type error -- a num where a bool is required (HOL4 rejects it). *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "neg_typeerror";
Theorem bad:
  (5:num) ==> T
Proof
  rw[]
QED
val _ = export_theory();
