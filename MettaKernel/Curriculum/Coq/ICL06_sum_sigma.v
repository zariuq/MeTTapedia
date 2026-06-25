(* ============================================================================
   ICL Ch.6 — Sum and Sigma Types   (MeTTaKernel curriculum, DTT ladder, Coq)
   Certifying decisions ({A}+{B}, sumbool) and dependent pairs ({x | P x}, sig).
   POSITIVES check with `coqc`; NEGATIVES via `Fail`.
   ========================================================================== *)

(* ---- A certifying decision procedure : decidable equality on nat ------------ *)
Definition nat_eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n as [| n IHn]; intros m; destruct m as [| m].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (IHn m) as [e | ne].
    + left; rewrite e; reflexivity.
    + right; intro h; injection h as h'; apply ne; exact h'.
Defined.

(* it really computes (informative content) *)
Definition nat_eqb (n m : nat) : bool :=
  match nat_eq_dec n m with left _ => true | right _ => false end.
Example nat_eqb_22 : nat_eqb 2 2 = true := eq_refl.
Example nat_eqb_23 : nat_eqb 2 3 = false := eq_refl.

(* ---- Sigma types : a value packaged with a proof about it ------------------- *)
Definition four_witness : { n : nat | n + n = 4 }.
Proof. exists 2. reflexivity. Defined.

Definition sig_val {A} {P : A -> Prop} (s : { x | P x }) : A :=
  match s with exist _ x _ => x end.

Example sig_val_four : sig_val four_witness = 2 := eq_refl.

(* projecting the certificate (a proof) from the package *)
Definition sig_cert {A} {P : A -> Prop} (s : { x | P x }) : P (sig_val s) :=
  match s with exist _ _ p => p end.

(* ---- NEGATIVE : the certificate must actually prove the property ------------ *)
Fail Definition bad_witness : { n : nat | n + n = 5 } := exist _ 2 eq_refl.

(* ---- a decidable equality yields a correct boolean test -------------------- *)
Lemma nat_eqb_refl : forall n, nat_eqb n n = true.
Proof. intro n. unfold nat_eqb. destruct (nat_eq_dec n n) as [e | ne]. - reflexivity. - exfalso; apply ne; reflexivity. Qed.

(* ---- combining certifying decisions ---------------------------------------- *)
Definition sumbool_and {A B : Prop} (da : {A} + {~ A}) (db : {B} + {~ B}) :
  {A /\ B} + {~ (A /\ B)}.
Proof.
  destruct da as [a | na].
  - destruct db as [b | nb].
    + left; split; assumption.
    + right; intros [_ b]; apply nb; exact b.
  - right; intros [a _]; apply na; exact a.
Defined.

(* ---- sigT : a dependent pair whose SECOND type depends on the first --------- *)
Definition dep : { b : bool & if b then nat else bool } := existT _ true 5.
Example dep_fst : projT1 dep = true := eq_refl.
Example dep_snd : projT2 dep = 5 := eq_refl.

(* ---- NEGATIVE : a sigT certificate must hold for the chosen witness --------- *)
Fail Definition bad_dep : { n : nat & n = 5 } := existT _ 2 eq_refl.
