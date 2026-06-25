(* NEGATIVE: a type error -- num cannot be conjoined with bool (HOL is typed). *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "neg_typeerror";
val bad = “(1:num) /\ T”;
val _ = export_theory();
