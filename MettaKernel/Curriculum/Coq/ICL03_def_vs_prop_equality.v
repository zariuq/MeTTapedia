(* ============================================================================
   ICL Ch.3 — Definitional and Propositional Equality
   (MeTTaKernel curriculum, DTT ladder, Coq)
   Definitional equality = computation (conversion); propositional equality `=`
   is reasoned about with discriminate / injection / rewrite.
   POSITIVES check with `coqc`; NEGATIVES via `Fail`.
   ========================================================================== *)

(* ---- The conversion principle: `eq_refl` works up to computation ------------ *)
Example conv_compute : 2 + 2 = 4 := eq_refl.            (* 2+2 reduces to 4 *)
Example conv_beta    : (fun x : nat => x) 7 = 7 := eq_refl.

(* ---- Disjointness of constructors (discriminate) ---------------------------- *)
Lemma true_neq_false : true <> false.
Proof. discriminate. Qed.

Lemma O_neq_S : forall n, 0 <> S n.
Proof. discriminate. Qed.

(* ---- Injectivity of constructors (injection) -------------------------------- *)
Lemma S_inj : forall m n, S m = S n -> m = n.
Proof. intros m n e. injection e as e'. exact e'. Qed.

(* ---- A boolean equality test and its propositional specification ------------ *)
Definition eqb (x y : bool) : bool :=
  match x, y with true, true => true | false, false => true | _, _ => false end.

Lemma eqb_true_iff : forall x y, eqb x y = true <-> x = y.
Proof.
  intros x y. split.
  - destruct x, y; simpl; intro h; try reflexivity; discriminate.
  - intro e. rewrite e. destruct y; reflexivity.
Qed.

(* ---- Cantor's theorem: no surjection nat -> (nat -> bool) ------------------- *)
Lemma cantor : forall f : nat -> (nat -> bool), exists g, forall n, f n <> g.
Proof.
  intros f. exists (fun n => negb (f n n)). intros n e.
  pose proof (f_equal (fun h => h n) e) as H. simpl in H.
  destruct (f n n); discriminate.
Qed.

(* ---- NEGATIVES : the checker rejects bad equality reasoning ----------------- *)
(* a non-convertible (false) equation cannot be closed by `eq_refl` *)
Fail Example bad_conv : 2 + 2 = 5 := eq_refl.
(* distinct constructors are not propositionally equal *)
Fail Example bad_bool : true = false := eq_refl.
