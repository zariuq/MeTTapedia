(* HOL05 - classical reasoning (HOL is classical by construction). *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "HOL05_classical";

Theorem excluded_middle:
  !P. P \/ ~P
Proof
  metis_tac[]
QED

Theorem double_neg:
  !P. ~~P <=> P
Proof
  metis_tac[]
QED

Theorem peirce:
  !P Q. ((P ==> Q) ==> P) ==> P
Proof
  metis_tac[]
QED

val _ = export_theory();
