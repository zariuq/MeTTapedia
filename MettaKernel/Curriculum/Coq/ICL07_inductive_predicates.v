(* ============================================================================
   ICL Ch.7 — Inductive Predicates   (MeTTaKernel curriculum, DTT ladder, Coq)
   Predicates defined by inference rules (constructors); proofs by induction on
   the derivation.  POSITIVES check with `coqc`; NEGATIVES via `Fail`.
   ========================================================================== *)

(* ---- Evenness as an inductive predicate ------------------------------------- *)
Inductive even : nat -> Prop :=
| ev0  : even 0
| evSS : forall n, even n -> even (S (S n)).

Lemma even_4 : even 4.
Proof. repeat constructor. Qed.

(* induction on the derivation of `even n` *)
Lemma even_plus : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn' IH]; simpl.
  - exact Hm.
  - apply evSS. exact IH.
Qed.

(* ---- The order relation `<=` as an inductive predicate ---------------------- *)
Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, le n m -> le n (S m).

Lemma le_0_n : forall n, le 0 n.
Proof. induction n as [| n IH]. - apply le_n. - apply le_S. exact IH. Qed.

Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
Proof.
  intros a b c Hab Hbc. generalize dependent a.
  induction Hbc; intros a Hab.
  - exact Hab.
  - apply le_S. apply IHHbc. exact Hab.
Qed.

(* ---- NEGATIVE : an unprovable instance has no proof term -------------------- *)
(* `evSS 1 ev0` would need `even 1` but `ev0 : even 0` — rejected *)
Fail Definition even_3 : even 3 := evSS 1 ev0.

(* ---- Inversion : reading information back out of a derivation --------------- *)
Lemma even_SS_inv : forall n, even (S (S n)) -> even n.
Proof. intros n H. inversion H. assumption. Qed.

Lemma not_even_1 : ~ even 1.
Proof. intro H. inversion H. Qed.

(* ---- a recursively-defined doubling is always even ------------------------- *)
Fixpoint double (n : nat) : nat :=
  match n with 0 => 0 | S k => S (S (double k)) end.

Lemma even_double : forall n, even (double n).
Proof. intro n. induction n as [| n IH]; simpl. - apply ev0. - apply evSS. exact IH. Qed.

(* ---- monotonicity of `<=` --------------------------------------------------- *)
Lemma le_refl : forall n, le n n.
Proof. intro n. apply le_n. Qed.

Lemma le_n_S : forall n m, le n m -> le (S n) (S m).
Proof. intros n m H. induction H as [k | k l Hkl IH]. - apply le_n. - apply le_S. exact IH. Qed.
