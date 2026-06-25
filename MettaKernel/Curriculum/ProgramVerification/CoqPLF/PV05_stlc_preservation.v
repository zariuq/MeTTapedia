(* ============================================================================
   Program Verification / CoqPLF — STLC PRESERVATION (with the substitution lemma)
   (MeTTaKernel curriculum; self-contained vanilla Rocq/Coq 9.1.  Companion to
   stlc.v.  Spine after Software Foundations PLF "StlcProp": appears_free_in,
   context invariance, substitution preserves typing, preservation.)
   ========================================================================== *)

From Stdlib Require Import Nat Arith.

Inductive ty : Type := TBase | TArrow (A B : ty).
Inductive tm : Type := Var (x : nat) | App (f a : tm) | Abs (x : nat) (T : ty) (body : tm).

Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | Var y      => if Nat.eqb x y then s else Var y
  | App f a    => App (subst x s f) (subst x s a)
  | Abs y T b  => if Nat.eqb x y then Abs y T b else Abs y T (subst x s b)
  end.

Inductive value : tm -> Prop := v_abs : forall x T b, value (Abs x T b).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T b v, value v -> step (App (Abs x T b) v) (subst x v b)
| ST_App1   : forall f f' a, step f f' -> step (App f a) (App f' a)
| ST_App2   : forall v a a', value v -> step a a' -> step (App v a) (App v a').

Definition context := nat -> option ty.
Definition empty : context := fun _ => None.
Definition update (G : context) (x : nat) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else G y.

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall G x T, G x = Some T -> has_type G (Var x) T
| T_Abs : forall G x T1 T2 b, has_type (update G x T1) b T2 -> has_type G (Abs x T1 b) (TArrow T1 T2)
| T_App : forall G f a T1 T2, has_type G f (TArrow T1 T2) -> has_type G a T1 -> has_type G (App f a) T2.

(* ---- update map lemmas ----------------------------------------------------- *)
Lemma update_eq : forall G x T, update G x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall G x y T, x <> y -> update G x T y = G y.
Proof. intros G x y T H. unfold update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction. - reflexivity. Qed.

(* ---- free variables + context invariance ----------------------------------- *)
Inductive afi : nat -> tm -> Prop :=
| afi_var  : forall x, afi x (Var x)
| afi_app1 : forall x f a, afi x f -> afi x (App f a)
| afi_app2 : forall x f a, afi x a -> afi x (App f a)
| afi_abs  : forall x y T b, x <> y -> afi x b -> afi x (Abs y T b).

Lemma context_invariance : forall G G' t T,
  has_type G t T -> (forall x, afi x t -> G x = G' x) -> has_type G' t T.
Proof.
  intros G G' t T HT. generalize dependent G'.
  induction HT as [G x T Hx | G x T1 T2 b Hb IH | G f a T1 T2 Hf IHf Ha IHa];
    intros G' Hagree.
  - apply T_Var. rewrite <- Hagree. exact Hx. apply afi_var.
  - apply T_Abs. apply IH. intros y Hy. unfold update.
    destruct (Nat.eqb x y) eqn:E.
    + reflexivity.
    + apply Hagree. apply afi_abs. apply Nat.eqb_neq in E. exact (fun h => E (eq_sym h)). exact Hy.
  - apply T_App with T1.
    + apply IHf. intros y Hy. apply Hagree. apply afi_app1. exact Hy.
    + apply IHa. intros y Hy. apply Hagree. apply afi_app2. exact Hy.
Qed.

Lemma free_in_context : forall x t T G, afi x t -> has_type G t T -> exists T', G x = Some T'.
Proof.
  intros x t T G Hafi. generalize dependent T. generalize dependent G.
  induction Hafi as [z | z f a Hf IH | z f a Ha IH | z y T0 b Hzy Hsub IH];
    intros G S HT; inversion HT; subst.
  - exists S. assumption.
  - eapply IH; eassumption.
  - eapply IH; eassumption.
  - destruct (IH _ _ ltac:(eassumption)) as [T' HT'].
    unfold update in HT'. destruct (Nat.eqb y z) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + exists T'. exact HT'.
Qed.

(* a closed term (typed in empty) types in any context *)
Lemma typable_empty_closed : forall t T, has_type empty t T -> forall x, ~ afi x t.
Proof.
  intros t T HT x Hafi.
  destruct (free_in_context x t T empty Hafi HT) as [T' HT']. discriminate HT'.
Qed.

(* ---- the SUBSTITUTION LEMMA ------------------------------------------------ *)
Lemma subst_preserves_typing : forall G x U t v T,
  has_type (update G x U) t T -> has_type empty v U -> has_type G (subst x v t) T.
Proof.
  intros G x U t v T Ht Hv. generalize dependent T. generalize dependent G.
  induction t as [y | f IHf a IHa | y T0 b IHb]; intros G T Ht; simpl; inversion Ht; subst.
  - (* Var y *)
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite update_eq in H1. injection H1 as H1; subst.
      apply context_invariance with empty.
      * exact Hv.
      * intros z Hz. exfalso. apply (typable_empty_closed v T Hv z). exact Hz.
    + apply T_Var. rewrite update_neq in H1. exact H1. apply Nat.eqb_neq in E. exact E.
  - (* App *)
    apply T_App with T1.
    + apply IHf. exact H2.
    + apply IHa. exact H4.
  - (* Abs y T0 b *)
    destruct (Nat.eqb x y) eqn:E.
    + (* x = y : the binder shadows the substitution *)
      apply Nat.eqb_eq in E; subst.
      apply T_Abs. apply context_invariance with (update (update G y U) y T0).
      * exact H4.
      * intros z Hz. unfold update. destruct (Nat.eqb y z) eqn:E2; reflexivity.
    + (* x <> y : substitute under the binder *)
      apply T_Abs. apply IHb.
      apply context_invariance with (update (update G x U) y T0).
      * exact H4.
      * intros z Hz. unfold update.
        destruct (Nat.eqb y z) eqn:Eyz; destruct (Nat.eqb x z) eqn:Exz; try reflexivity.
        apply Nat.eqb_eq in Eyz; subst. apply Nat.eqb_eq in Exz; subst.
        apply Nat.eqb_neq in E. contradiction.
Qed.

(* ---- PRESERVATION ---------------------------------------------------------- *)
Theorem preservation : forall t t' T, has_type empty t T -> step t t' -> has_type empty t' T.
Proof.
  intros t t' T HT Hstep. generalize dependent T.
  induction Hstep; intros S HT; inversion HT; subst.
  - (* ST_AppAbs : App (Abs x T0 b) v --> subst x v b *)
    match goal with | [ H : has_type _ (Abs _ _ _) _ |- _ ] => inversion H; subst end.
    eapply subst_preserves_typing; eassumption.
  - (* ST_App1 *) eapply T_App. apply IHHstep; eassumption. eassumption.
  - (* ST_App2 *) eapply T_App. eassumption. apply IHHstep; eassumption.
Qed.

(* NEGATIVE: Abs is ternary -- under-application is rejected *)
Fail Definition neg_bad_abs : tm := Abs 0 TBase.
