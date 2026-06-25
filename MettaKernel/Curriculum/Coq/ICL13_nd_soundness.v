(* ============================================================================
   ICL Ch.10-11 bridge — SOUNDNESS of natural deduction w.r.t. boolean semantics
   (MeTTaKernel curriculum, DTT ladder, Coq).  Connects the ND calculus to the
   models: every derivable sequent is semantically valid.  (Completeness, the
   converse, is the harder direction, developed in ICL14.)
   ========================================================================== *)

From Stdlib Require Import List Bool.
Import ListNotations.

Inductive form : Type :=
| FVar (n : nat) | Bot
| Imp (a b : form) | And (a b : form) | Or (a b : form).

(* natural deduction (as in ICL10) *)
Inductive nd : list form -> form -> Prop :=
| nd_ax    : forall G a, In a G -> nd G a
| nd_impI  : forall G a b, nd (a :: G) b -> nd G (Imp a b)
| nd_impE  : forall G a b, nd G (Imp a b) -> nd G a -> nd G b
| nd_andI  : forall G a b, nd G a -> nd G b -> nd G (And a b)
| nd_andE1 : forall G a b, nd G (And a b) -> nd G a
| nd_andE2 : forall G a b, nd G (And a b) -> nd G b
| nd_orI1  : forall G a b, nd G a -> nd G (Or a b)
| nd_orI2  : forall G a b, nd G b -> nd G (Or a b)
| nd_orE   : forall G a b c, nd G (Or a b) -> nd (a :: G) c -> nd (b :: G) c -> nd G c
| nd_botE  : forall G a, nd G Bot -> nd G a.

(* boolean semantics (as in ICL11) *)
Fixpoint eval (v : nat -> bool) (f : form) : bool :=
  match f with
  | FVar n  => v n
  | Bot     => false
  | Imp a b => implb (eval v a) (eval v b)
  | And a b => andb  (eval v a) (eval v b)
  | Or  a b => orb   (eval v a) (eval v b)
  end.

Definition models (v : nat -> bool) (G : list form) : Prop :=
  forall p, In p G -> eval v p = true.

(* ---- SOUNDNESS : derivable implies valid in every model ------------------- *)
Theorem nd_sound : forall G a, nd G a -> forall v, models v G -> eval v a = true.
Proof.
  intros G a D.
  induction D as
    [ G p Hin | G p q D IH | G p q D1 IH1 D2 IH2 | G p q D1 IH1 D2 IH2
    | G p q D IH | G p q D IH | G p q D IH | G p q D IH
    | G p q r D1 IH1 D2 IH2 D3 IH3 | G p D IH ]; intros v Hm; simpl.
  - (* ax *) apply Hm. exact Hin.
  - (* impI *) destruct (eval v p) eqn:Ep; simpl.
    + apply IH. intros x [Hx | Hx]. rewrite <- Hx. exact Ep. apply Hm. exact Hx.
    + reflexivity.
  - (* impE *) specialize (IH1 v Hm). specialize (IH2 v Hm).
    simpl in IH1. rewrite IH2 in IH1. exact IH1.
  - (* andI *) rewrite (IH1 v Hm). rewrite (IH2 v Hm). reflexivity.
  - (* andE1 *) specialize (IH v Hm). simpl in IH.
    destruct (eval v p); destruct (eval v q); simpl in IH; try discriminate; reflexivity.
  - (* andE2 *) specialize (IH v Hm). simpl in IH.
    destruct (eval v p); destruct (eval v q); simpl in IH; try discriminate; reflexivity.
  - (* orI1 *) rewrite (IH v Hm). reflexivity.
  - (* orI2 *) rewrite (IH v Hm). destruct (eval v p); reflexivity.
  - (* orE *) specialize (IH1 v Hm). simpl in IH1.
    destruct (eval v p) eqn:Ep.
    + apply IH2. intros x [Hx | Hx]. rewrite <- Hx. exact Ep. apply Hm. exact Hx.
    + destruct (eval v q) eqn:Eq.
      * apply IH3. intros x [Hx | Hx]. rewrite <- Hx. exact Eq. apply Hm. exact Hx.
      * simpl in IH1. discriminate.
  - (* botE *) specialize (IH v Hm). simpl in IH. discriminate.
Qed.

(* corollary: a closed derivation yields a tautology *)
Corollary nd_closed_valid : forall a, nd nil a -> forall v, eval v a = true.
Proof. intros a D v. apply (nd_sound nil a D v). intros p []. Qed.

(* NEGATIVE: Bot is never true under any valuation -- the checker rejects the false claim *)
Fail Example neg_bot_true : eval (fun _ => true) Bot = true := eq_refl.
