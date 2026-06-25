(* ============================================================================
   ICL Ch.4 — Induction and Recursion   (MeTTaKernel curriculum, DTT ladder, Coq)
   Induction lemmas reproved from the computation rules; primitive recursion with
   an equational specification; size/strong induction.
   POSITIVES check with `coqc`; NEGATIVES via `Fail`.
   ========================================================================== *)

(* ---- Induction lemmas for + (the classic three-step dance) ------------------ *)
Lemma add_0_r : forall n, n + 0 = n.
Proof. induction n as [| n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma add_succ_r : forall n m, n + S m = S (n + m).
Proof. intros n m. induction n as [| n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma add_comm : forall n m, n + m = m + n.
Proof.
  intros n m. induction n as [| n IH]; simpl.
  - rewrite add_0_r. reflexivity.
  - rewrite IH. rewrite add_succ_r. reflexivity.
Qed.

Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
Proof. intros n m p. induction n as [| n IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

(* ---- Primitive recursion + equational specification ------------------------- *)
Fixpoint double (n : nat) : nat :=
  match n with 0 => 0 | S k => S (S (double k)) end.

Example double_compute : double 3 = 6 := eq_refl.

Lemma double_spec : forall n, double n = n + n.
Proof.
  induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite add_succ_r. reflexivity.
Qed.

(* ---- Size / strong (course-of-values) induction ----------------------------- *)
From Stdlib Require Import Wf_nat.

Lemma strong_induction : forall P : nat -> Prop,
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof. intros P H n. exact (lt_wf_ind n P H). Qed.

(* ---- NEGATIVE : a non-structural recursion is rejected (guard checker) ------- *)
Fail Fixpoint bad (n : nat) : nat := S (bad n).
