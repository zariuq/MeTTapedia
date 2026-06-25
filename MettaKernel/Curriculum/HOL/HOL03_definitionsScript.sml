(* HOL03 - definitions: recursive function, algebraic Datatype, Inductive relation. *)
open HolKernel Parse boolLib bossLib;
val _ = new_theory "HOL03_definitions";

Definition dbl_def:
  (dbl 0 = 0) /\
  (dbl (SUC n) = SUC (SUC (dbl n)))
End

Theorem dbl_two:
  dbl 2 = 4
Proof
  EVAL_TAC
QED

Datatype:
  tree = Leaf | Node tree num tree
End

Definition tsize_def:
  (tsize Leaf = 0) /\
  (tsize (Node l n r) = 1 + tsize l + tsize r)
End

Theorem tsize_node:
  tsize (Node Leaf 5 Leaf) = 1
Proof
  EVAL_TAC
QED

Inductive ev:
  ev 0 /\
  (!n. ev n ==> ev (SUC (SUC n)))
End

Theorem ev_ss0:
  ev (SUC (SUC 0))
Proof
  metis_tac[ev_rules]
QED

val _ = export_theory();
