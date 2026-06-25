(* Cross-system smoke (Coq): the same tiny theorems proved in all three checkers. *)
Theorem imp_id : forall P : Prop, P -> P.
Proof. intros P p. exact p. Qed.
Theorem and_elim_l : forall P Q : Prop, P /\ Q -> P.
Proof. intros P Q [p _]. exact p. Qed.
Theorem ex_falso : forall P : Prop, False -> P.
Proof. intros P f. destruct f. Qed.
Theorem eq_refl_ex : forall (A : Type) (a : A), a = a.
Proof. reflexivity. Qed.
Theorem cong : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof. intros A B f x y e. rewrite e. reflexivity. Qed.
Theorem pair_proj : forall (A B : Type) (a : A) (b : B), fst (a, b) = a.
Proof. reflexivity. Qed.
