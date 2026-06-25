(* HOL04 - higher-order quantification + the Hilbert choice operator @ (SELECT). *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "HOL04_higher_order";

Theorem pred_mono:
  !(P:'a -> bool) Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)
Proof
  metis_tac[]
QED

Theorem select_intro:
  !(P:'a -> bool) x. P x ==> P (@y. P y)
Proof
  metis_tac[SELECT_AX]
QED

val _ = export_theory();
