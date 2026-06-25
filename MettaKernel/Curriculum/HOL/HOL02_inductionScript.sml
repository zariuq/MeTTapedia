(* HOL02 - induction (Induct / Cases_on) over num and list. *)
open HolKernel Parse boolLib bossLib arithmeticTheory listTheory;
val _ = new_theory "HOL02_induction";

Theorem add_comm_ind:
  !m n:num. m + n = n + m
Proof
  Induct >> rw[]
QED

Theorem length_append:
  !xs ys:'a list. LENGTH (xs ++ ys) = LENGTH xs + LENGTH ys
Proof
  Induct >> rw[]
QED

Theorem rev_rev:
  !xs:'a list. REVERSE (REVERSE xs) = xs
Proof
  Induct >> rw[]
QED

val _ = export_theory();
