(* ============================================================================
   Program Verification / CoqPLF — the REAL simply-typed lambda calculus (STLC)
   with binders + capture-substitution, and TYPE SAFETY (progress this file;
   preservation + the substitution lemma in stlc_preservation.v).
   (MeTTaKernel curriculum; self-contained vanilla Rocq/Coq 9.1.  Spine after
   Software Foundations PLF "Stlc"/"StlcProp", variables = nat ids.)
   This is NOT the binder-free `types_safety.v` prelude -- it has real lambda/app.
   ========================================================================== *)

From Stdlib Require Import Nat.

(* ---- Types and terms (named variables = nat) ------------------------------- *)
Inductive ty : Type := TBase | TArrow (A B : ty).

Inductive tm : Type :=
| Var (x : nat)
| App (f a : tm)
| Abs (x : nat) (T : ty) (body : tm).

(* ---- Values ---------------------------------------------------------------- *)
Inductive value : tm -> Prop :=
| v_abs : forall x T b, value (Abs x T b).

(* ---- Capture-substitution  [x := s] t  (SF-style; exact for closed s) ------- *)
Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | Var y      => if Nat.eqb x y then s else Var y
  | App f a    => App (subst x s f) (subst x s a)
  | Abs y T b  => if Nat.eqb x y then Abs y T b else Abs y T (subst x s b)
  end.

(* ---- Small-step call-by-value semantics ------------------------------------ *)
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T b v, value v -> step (App (Abs x T b) v) (subst x v b)
| ST_App1   : forall f f' a, step f f' -> step (App f a) (App f' a)
| ST_App2   : forall v a a', value v -> step a a' -> step (App v a) (App v a').

(* ---- Typing contexts as total maps  nat -> option ty ----------------------- *)
Definition context := nat -> option ty.
Definition empty : context := fun _ => None.
Definition update (G : context) (x : nat) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else G y.

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall G x T, G x = Some T -> has_type G (Var x) T
| T_Abs : forall G x T1 T2 b, has_type (update G x T1) b T2 -> has_type G (Abs x T1 b) (TArrow T1 T2)
| T_App : forall G f a T1 T2, has_type G f (TArrow T1 T2) -> has_type G a T1 -> has_type G (App f a) T2.

(* ---- Canonical forms : a closed value of arrow type is a lambda ------------- *)
Lemma canonical_arrow : forall t T1 T2,
  value t -> has_type empty t (TArrow T1 T2) -> exists x b, t = Abs x T1 b.
Proof.
  intros t T1 T2 Hv HT. destruct Hv as [x T b]. inversion HT; subst.
  exists x, b. reflexivity.
Qed.

(* ---- PROGRESS : a closed well-typed term is a value or it steps ------------- *)
Theorem progress : forall t T, has_type empty t T -> value t \/ exists t', step t t'.
Proof.
  intros t T HT. remember empty as G eqn:HG.
  induction HT as [G x T Hx | G x T1 T2 b Hb IH | G f a T1 T2 Hf IHf Ha IHa]; subst.
  - (* Var: impossible in the empty context *)
    discriminate Hx.
  - (* Abs is a value *)
    left. apply v_abs.
  - (* App: use IH on the function and argument *)
    right.
    destruct (IHf eq_refl) as [Hvf | [f' Hsf]].
    + destruct (canonical_arrow f T1 T2 Hvf Hf) as [x [b Hfeq]]. subst f.
      destruct (IHa eq_refl) as [Hva | [a' Hsa]].
      * exists (subst x a b). apply ST_AppAbs. exact Hva.
      * exists (App (Abs x T1 b) a'). apply ST_App2. apply v_abs. exact Hsa.
    + exists (App f' a). apply ST_App1. exact Hsf.
Qed.

(* NEGATIVE: Abs is ternary (x, type, body) -- under-application is rejected *)
Fail Definition neg_bad_abs : tm := Abs 0 TBase.
