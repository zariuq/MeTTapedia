(* ============================================================================
   ICL Ch.5 — Truth-Value Semantics and the Elimination Restriction
   (MeTTaKernel curriculum, DTT ladder, Coq)
   A `Prop` may be eliminated to prove another `Prop`, but NOT to build data
   (Type/Set) — the elimination restriction.  `sumbool` is the data-level analogue.
   POSITIVES check with `coqc`; NEGATIVES via `Fail`.
   ========================================================================== *)

(* ---- Eliminating a Prop to prove a Prop is allowed -------------------------- *)
Lemma or_comm_prop : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof. intros P Q [p | q]. - right; exact p. - left; exact q. Qed.

(* ---- NEGATIVE : eliminating a Prop (\/) to build data (nat) is FORBIDDEN ----- *)
Fail Definition prop_to_data (P Q : Prop) (h : P \/ Q) : nat :=
  match h with or_introl _ => 0 | or_intror _ => 1 end.

(* ---- sumbool {A}+{B} : the informative, data-eliminable analogue ------------ *)
Definition pick {A B : Prop} (h : {A} + {B}) : nat :=
  match h with left _ => 0 | right _ => 1 end.

(* ---- Truth-value semantics : a boolean decides its own proposition ---------- *)
Lemma bool_value : forall b : bool, {b = true} + {b = false}.
Proof. destruct b. - left; reflexivity. - right; reflexivity. Qed.

Definition is_true (b : bool) : Prop := b = true.

Lemma negb_true : forall b, is_true (negb b) <-> ~ is_true b.
Proof.
  intros b. unfold is_true. destruct b; simpl; split.
  - intro h; discriminate.
  - intro h; exfalso; apply h; reflexivity.
  - intros _; discriminate.
  - intros _; reflexivity.
Qed.

(* ---- Eliminating a Prop to prove a Prop is allowed -------------------------- *)
Lemma and_proj : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q [p _]. exact p. Qed.

Lemma ex_not_forall_not : forall (P : nat -> Prop), (exists n, P n) -> ~ (forall n, ~ P n).
Proof. intros P [n hn] h. exact (h n hn). Qed.

(* ---- Decidability lives in the DATA world (sumbool), not in Prop ------------ *)
Lemma bool_dec' : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof. intros [] []. - left; reflexivity. - right; discriminate. - right; discriminate. - left; reflexivity. Qed.

Lemma is_true_dec : forall b : bool, {is_true b} + {~ is_true b}.
Proof. intros b. unfold is_true. destruct b. - left; reflexivity. - right; discriminate. Qed.

(* ---- NEGATIVE : projecting the WITNESS of an `exists` into data is FORBIDDEN - *)
(* (`and` is singleton-eliminable, but `ex` carries a data witness that may not escape) *)
Fail Definition ex_witness (P : nat -> Prop) (h : exists n, P n) : nat :=
  match h with ex_intro _ n _ => n end.
