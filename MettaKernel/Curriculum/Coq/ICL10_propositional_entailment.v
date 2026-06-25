(* ============================================================================
   ICL Ch.10 — Propositional Entailment: Natural Deduction + Hilbert
   (MeTTaKernel curriculum, DTT ladder, Coq)
   An intuitionistic ND calculus (context |- formula) with intro/elim rules for
   every connective, weakening (context monotonicity), several derivations, the
   Glivenko-flavored ~~(a \/ ~a), and a Hilbert system deriving a -> a.
   ========================================================================== *)

From Stdlib Require Import List.
Import ListNotations.

(* ---- Propositional formulas ------------------------------------------------ *)
Inductive form : Type :=
| FVar (n : nat)
| Bot
| Imp (a b : form)
| And (a b : form)
| Or  (a b : form).

Definition Neg (a : form) : form := Imp a Bot.

(* ---- Natural deduction:  G |- a  ------------------------------------------- *)
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

(* ---- Weakening / context monotonicity (a real metatheorem) ----------------- *)
Lemma nd_mono : forall G a, nd G a -> forall G', (forall x, In x G -> In x G') -> nd G' a.
Proof.
  intros G a D.
  induction D as
    [ G0 p Hin
    | G0 p q D IHD
    | G0 p q D1 IHD1 D2 IHD2
    | G0 p q D1 IHD1 D2 IHD2
    | G0 p q D IHD
    | G0 p q D IHD
    | G0 p q D IHD
    | G0 p q D IHD
    | G0 p q r D1 IHD1 D2 IHD2 D3 IHD3
    | G0 p D IHD ]; intros G' Hsub.
  - apply nd_ax. apply Hsub. exact Hin.
  - apply nd_impI. apply IHD. intros x [E | Hx]. + left; exact E. + right; apply Hsub; exact Hx.
  - eapply nd_impE. + apply IHD1; exact Hsub. + apply IHD2; exact Hsub.
  - apply nd_andI. + apply IHD1; exact Hsub. + apply IHD2; exact Hsub.
  - eapply nd_andE1. apply IHD; exact Hsub.
  - eapply nd_andE2. apply IHD; exact Hsub.
  - apply nd_orI1. apply IHD; exact Hsub.
  - apply nd_orI2. apply IHD; exact Hsub.
  - eapply nd_orE.
    + apply IHD1; exact Hsub.
    + apply IHD2. intros x [E | Hx]. left; exact E. right; apply Hsub; exact Hx.
    + apply IHD3. intros x [E | Hx]. left; exact E. right; apply Hsub; exact Hx.
  - apply nd_botE. apply IHD; exact Hsub.
Qed.

(* ---- Derivations ----------------------------------------------------------- *)
Lemma nd_id : forall a, nd nil (Imp a a).
Proof. intro a. apply nd_impI. apply nd_ax. simpl. left. reflexivity. Qed.

Lemma nd_k : forall a b, nd nil (Imp a (Imp b a)).
Proof. intros a b. apply nd_impI. apply nd_impI. apply nd_ax. simpl. right. left. reflexivity. Qed.

Lemma nd_and_comm : forall a b, nd nil (Imp (And a b) (And b a)).
Proof.
  intros a b. apply nd_impI. apply nd_andI.
  - eapply nd_andE2. apply nd_ax. simpl. left. reflexivity.
  - eapply nd_andE1. apply nd_ax. simpl. left. reflexivity.
Qed.

(* the Glivenko-flavored intuitionistic theorem ~~(a \/ ~a) *)
Lemma nd_dne_lem : forall a, nd nil (Neg (Neg (Or a (Neg a)))).
Proof.
  intro a. apply nd_impI.
  apply nd_impE with (Or a (Neg a)).
  - apply nd_ax. simpl. left. reflexivity.
  - apply nd_orI2. apply nd_impI.
    apply nd_impE with (Or a (Neg a)).
    + apply nd_ax. simpl. right. left. reflexivity.
    + apply nd_orI1. apply nd_ax. simpl. left. reflexivity.
Qed.

(* ---- A Hilbert system (K, S, modus ponens) deriving  a -> a ---------------- *)
Inductive hil : form -> Prop :=
| h_K  : forall a b, hil (Imp a (Imp b a))
| h_S  : forall a b c, hil (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))
| h_MP : forall a b, hil (Imp a b) -> hil a -> hil b.

Lemma hil_id : forall a, hil (Imp a a).
Proof.
  intro a. apply h_MP with (Imp a (Imp a a)).
  - apply h_MP with (Imp a (Imp (Imp a a) a)).
    + apply h_S.
    + apply h_K.
  - apply h_K.
Qed.

(* ---- NEGATIVE : `Imp` is binary --------------------------------------------- *)
Fail Definition bad_form : form := Imp (FVar 0).
