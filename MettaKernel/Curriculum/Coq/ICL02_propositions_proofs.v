(* ============================================================================
   ICL Ch.2 — Propositions and Proofs   (MeTTaKernel curriculum, DTT ladder, Coq)
   Uses Rocq's prelude logic (Prop, ->, forall, /\, \/, exists, False, ~, =).
   POSITIVES check with `coqc`; NEGATIVES are demonstrated inline with `Fail`.
   The slogan: a proof of P is a *term of type P* (propositions-as-types).
   ========================================================================== *)

(* ---- Implication & ∀ are functions; a proof term is a lambda ---------------- *)
Definition imp_refl (P : Prop) : P -> P := fun p => p.

Lemma imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof. intros P Q R f g p. apply g. apply f. exact p. Qed.

Definition modus_ponens (P Q : Prop) (f : P -> Q) (p : P) : Q := f p.

(* ---- Conjunction : intro (split) and elim (destruct) ------------------------ *)
Lemma and_intro : forall P Q : Prop, P -> Q -> P /\ Q.
Proof. intros P Q p q. split; assumption. Qed.

Lemma and_comm' : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof. intros P Q [p q]. split; assumption. Qed.

(* ---- Disjunction : intro (left/right) and elim (case) ----------------------- *)
Lemma or_comm' : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof. intros P Q [p | q]. - right; exact p. - left; exact q. Qed.

(* ---- Falsity and negation --------------------------------------------------- *)
Lemma False_elim : forall P : Prop, False -> P.
Proof. intros P h. destruct h. Qed.

Lemma double_neg_intro : forall P : Prop, P -> ~ ~ P.
Proof. intros P p np. apply np. exact p. Qed.

(* ---- Leibniz equality : substitution of equals ------------------------------ *)
Lemma leibniz : forall (A : Type) (x y : A), x = y -> forall Q : A -> Prop, Q x -> Q y.
Proof. intros A x y e Q qx. rewrite <- e. exact qx. Qed.

(* ---- Existential quantification : witness intro, destruct elim --------------- *)
Lemma ex_intro_example : exists n : nat, n = 0.
Proof. exists 0. reflexivity. Qed.

Lemma ex_elim : forall (P : nat -> Prop) (Q : Prop),
  (exists n, P n) -> (forall n, P n -> Q) -> Q.
Proof. intros P Q [n pn] h. apply (h n). exact pn. Qed.

(* ---- An inductive proposition, proved by its constructors ------------------- *)
Inductive even : nat -> Prop :=
| even_O  : even 0
| even_SS : forall n, even n -> even (S (S n)).

Lemma even_4 : even 4.
Proof. apply even_SS. apply even_SS. apply even_O. Qed.

(* ---- Excluded middle : a classical axiom (NOT derivable intuitionistically) -- *)
Axiom XM : forall P : Prop, P \/ ~ P.

Lemma not_not_classical : forall P : Prop, ~ ~ P -> P.
Proof. intros P nnp. destruct (XM P) as [p | np]. - exact p. - destruct (nnp np). Qed.

(* ---- NEGATIVES : the checker rejects faulty proofs -------------------------- *)
(* a proof term offered at the wrong type *)
Fail Definition wrong_type (P Q : Prop) (p : P) : Q := p.
(* a proposition (a type) used where a proof (an inhabitant) is required *)
Fail Definition prop_as_proof (P : Prop) : P := P.
(* a false equation: the two sides are not convertible *)
Fail Example zero_is_one : 0 = 1 := eq_refl.
