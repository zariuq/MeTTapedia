(* NEGATIVE: an unprovable goal -- the tactic cannot close F, so QED is rejected. *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "neg_unprovable";
Theorem bad:
  F
Proof
  rw[]
QED
val _ = export_theory();
