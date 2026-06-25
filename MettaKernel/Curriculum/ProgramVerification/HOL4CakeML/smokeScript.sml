(* HOL4 bounded smoke: a verified function over the naturals (pure HOL4 core). *)
open HolKernel boolLib bossLib;
val _ = new_theory "smoke";

Definition dbl_def:
  dbl n = n + n
End

Theorem dbl_two:
  dbl 2 = 4
Proof
  rw[dbl_def]
QED

Theorem dbl_add:
  !m n. dbl (m + n) = dbl m + dbl n
Proof
  rw[dbl_def]
QED

val _ = export_theory();
