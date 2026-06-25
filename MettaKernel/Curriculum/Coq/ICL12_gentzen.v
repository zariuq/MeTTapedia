(* ============================================================================
   ICL Ch.12 — Gentzen Sequent Calculus (intuitionistic LJ)
   (MeTTaKernel curriculum, DTT ladder, Coq)
   A single-conclusion sequent calculus with LEFT and RIGHT rules (the feature
   distinguishing it from natural deduction), and several derivations including
   implication transitivity.
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.

Inductive form : Type :=
| FVar (n : nat) | Bot
| Imp (a b : form) | And (a b : form) | Or (a b : form).

(* ---- Sequents  G ==> a  ---------------------------------------------------- *)
Inductive seq : list form -> form -> Prop :=
| s_ax   : forall G a, In a G -> seq G a
| s_botL : forall G a, In Bot G -> seq G a
| s_impR : forall G a b, seq (a :: G) b -> seq G (Imp a b)
| s_impL : forall G a b c, In (Imp a b) G -> seq G a -> seq (b :: G) c -> seq G c
| s_andR : forall G a b, seq G a -> seq G b -> seq G (And a b)
| s_andL : forall G a b c, In (And a b) G -> seq (a :: b :: G) c -> seq G c
| s_orR1 : forall G a b, seq G a -> seq G (Or a b)
| s_orR2 : forall G a b, seq G b -> seq G (Or a b)
| s_orL  : forall G a b c, In (Or a b) G -> seq (a :: G) c -> seq (b :: G) c -> seq G c.

(* ---- Derivations ----------------------------------------------------------- *)
Lemma seq_id : forall a, seq nil (Imp a a).
Proof. intro a. apply s_impR. apply s_ax. simpl. left. reflexivity. Qed.

(* modus ponens as a sequent: from (a->b) and a derive b *)
Lemma seq_mp : forall a b, seq (Imp a b :: a :: nil) b.
Proof.
  intros a b. eapply s_impL.
  - simpl. left. reflexivity.
  - apply s_ax. simpl. right. left. reflexivity.
  - apply s_ax. simpl. left. reflexivity.
Qed.

Lemma seq_and_comm : forall a b, seq nil (Imp (And a b) (And b a)).
Proof.
  intros a b. apply s_impR. eapply s_andL.
  - simpl. left. reflexivity.
  - apply s_andR.
    + apply s_ax. simpl. right. left. reflexivity.
    + apply s_ax. simpl. left. reflexivity.
Qed.

(* transitivity of implication -- a genuine left/right interplay *)
Lemma seq_imp_trans : forall a b c,
  seq nil (Imp (Imp a b) (Imp (Imp b c) (Imp a c))).
Proof.
  intros a b c. apply s_impR. apply s_impR. apply s_impR.
  eapply s_impL.
  - simpl. right. left. reflexivity.
  - eapply s_impL.
    + simpl. right. right. left. reflexivity.
    + apply s_ax. simpl. left. reflexivity.
    + apply s_ax. simpl. left. reflexivity.
  - apply s_ax. simpl. left. reflexivity.
Qed.

(* ---- NEGATIVE : `Or` is binary --------------------------------------------- *)
Fail Definition bad_form : form := Or (FVar 0).
