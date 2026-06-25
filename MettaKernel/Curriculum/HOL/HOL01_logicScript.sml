(* HOL01 - logic and tactics (backward proof).  Core HOL4: classical Church STT. *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "HOL01_logic";

Theorem imp_id:
  !P. P ==> P
Proof
  rw[]
QED

Theorem and_comm_thm:
  !P Q. P /\ Q ==> Q /\ P
Proof
  rw[]
QED

Theorem or_comm_thm:
  !P Q. P \/ Q ==> Q \/ P
Proof
  metis_tac[]
QED

Theorem demorgan:
  !P Q. ~(P \/ Q) <=> ~P /\ ~Q
Proof
  metis_tac[]
QED

Theorem arith_decide:
  !n:num. n < n + 1
Proof
  decide_tac
QED

Theorem simp_zero:
  !n:num. n + 0 = n
Proof
  simp[]
QED

val _ = export_theory();
