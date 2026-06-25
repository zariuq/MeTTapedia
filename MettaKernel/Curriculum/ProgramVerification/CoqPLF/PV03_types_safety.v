(* ============================================================================
   Program Verification / CoqPLF — Type Safety: PROGRESS + PRESERVATION
   (MeTTaKernel curriculum, 4th pillar; self-contained vanilla Rocq/Coq 9.1.)
   A typed expression language (booleans + naturals) with small-step semantics,
   proving the two type-safety theorems.  Spine after Software Foundations PLF
   ("Types"): no binders, so progress+preservation are fully proved (no
   substitution lemma needed).  NEGATIVE inline via `Fail`.
   ========================================================================== *)

Inductive tm : Type :=
| ttrue | tfalse | tif (c t e : tm)
| tzero | tsucc (t : tm) | tpred (t : tm) | tiszero (t : tm).

Inductive bvalue : tm -> Prop := bv_true : bvalue ttrue | bv_false : bvalue tfalse.
Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue tzero
| nv_succ : forall t, nvalue t -> nvalue (tsucc t).
Definition value (t : tm) : Prop := bvalue t \/ nvalue t.

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue     : forall t e, step (tif ttrue t e) t
| ST_IfFalse    : forall t e, step (tif tfalse t e) e
| ST_If         : forall c c' t e, step c c' -> step (tif c t e) (tif c' t e)
| ST_Succ       : forall t t', step t t' -> step (tsucc t) (tsucc t')
| ST_PredZero   : step (tpred tzero) tzero
| ST_PredSucc   : forall t, nvalue t -> step (tpred (tsucc t)) t
| ST_Pred       : forall t t', step t t' -> step (tpred t) (tpred t')
| ST_IszeroZero : step (tiszero tzero) ttrue
| ST_IszeroSucc : forall t, nvalue t -> step (tiszero (tsucc t)) tfalse
| ST_Iszero     : forall t t', step t t' -> step (tiszero t) (tiszero t').

Inductive ty : Type := TBool | TNat.

Inductive has_type : tm -> ty -> Prop :=
| T_True   : has_type ttrue TBool
| T_False  : has_type tfalse TBool
| T_If     : forall c t e T, has_type c TBool -> has_type t T -> has_type e T -> has_type (tif c t e) T
| T_Zero   : has_type tzero TNat
| T_Succ   : forall t, has_type t TNat -> has_type (tsucc t) TNat
| T_Pred   : forall t, has_type t TNat -> has_type (tpred t) TNat
| T_Iszero : forall t, has_type t TNat -> has_type (tiszero t) TBool.

(* ---- Canonical forms ------------------------------------------------------- *)
Lemma bool_canonical : forall t, value t -> has_type t TBool -> bvalue t.
Proof. intros t [Hb | Hn] HT. - exact Hb. - destruct Hn; inversion HT. Qed.

Lemma nat_canonical : forall t, value t -> has_type t TNat -> nvalue t.
Proof. intros t [Hb | Hn] HT. - destruct Hb; inversion HT. - exact Hn. Qed.

(* ---- PROGRESS : a well-typed term is a value or it steps ------------------- *)
Theorem progress : forall t T, has_type t T -> value t \/ exists t', step t t'.
Proof.
  intros t T HT. induction HT.
  - left; left; apply bv_true.
  - left; left; apply bv_false.
  - right. destruct IHHT1 as [Hv | [c' Hs]].
    + assert (bvalue c) as Hb by (apply bool_canonical; assumption).
      destruct Hb as [|].
      * exists t; apply ST_IfTrue.
      * exists e; apply ST_IfFalse.
    + exists (tif c' t e); apply ST_If; exact Hs.
  - left; right; apply nv_zero.
  - destruct IHHT as [Hv | [t' Hs]].
    + left; right; apply nv_succ; apply nat_canonical; assumption.
    + right; exists (tsucc t'); apply ST_Succ; exact Hs.
  - right. destruct IHHT as [Hv | [t' Hs]].
    + assert (nvalue t) as Hn by (apply nat_canonical; assumption).
      destruct Hn as [| t0 Hn0].
      * exists tzero; apply ST_PredZero.
      * exists t0; apply ST_PredSucc; exact Hn0.
    + exists (tpred t'); apply ST_Pred; exact Hs.
  - right. destruct IHHT as [Hv | [t' Hs]].
    + assert (nvalue t) as Hn by (apply nat_canonical; assumption).
      destruct Hn as [| t0 Hn0].
      * exists ttrue; apply ST_IszeroZero.
      * exists tfalse; apply ST_IszeroSucc; exact Hn0.
    + exists (tiszero t'); apply ST_Iszero; exact Hs.
Qed.

(* ---- PRESERVATION : stepping preserves the type --------------------------- *)
Theorem preservation : forall t t' T, has_type t T -> step t t' -> has_type t' T.
Proof.
  intros t t' T HT. generalize dependent t'.
  induction HT; intros t' Hstep; inversion Hstep; subst.
  - assumption.
  - assumption.
  - apply T_If; try assumption. apply IHHT1; assumption.
  - apply T_Succ; apply IHHT; assumption.
  - apply T_Zero.
  - inversion HT; subst; assumption.
  - apply T_Pred; apply IHHT; assumption.
  - apply T_True.
  - apply T_False.
  - apply T_Iszero; apply IHHT; assumption.
Qed.

(* ---- NEGATIVE : ill-typed term (a number used where a boolean is needed) --- *)
Fail Definition bad : has_type (tsucc ttrue) TNat := T_Succ ttrue T_True.
