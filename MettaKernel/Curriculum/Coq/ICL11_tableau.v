(* ============================================================================
   ICL Ch.11 — Tableaux and Boolean Semantics   (MeTTaKernel curriculum, Coq)
   Boolean valuations, validity, and the soundness core of tableau refutation:
   a branch containing a formula and its negation is closed (has no model).
   ========================================================================== *)

From Stdlib Require Import List Bool.
Import ListNotations.

Inductive form : Type :=
| FVar (n : nat) | Bot
| Imp (a b : form) | And (a b : form) | Or (a b : form).
Definition Neg (a : form) : form := Imp a Bot.

(* ---- Boolean semantics ----------------------------------------------------- *)
Fixpoint eval (v : nat -> bool) (f : form) : bool :=
  match f with
  | FVar n  => v n
  | Bot     => false
  | Imp a b => implb (eval v a) (eval v b)
  | And a b => andb  (eval v a) (eval v b)
  | Or  a b => orb   (eval v a) (eval v b)
  end.

Definition valid (f : form) : Prop := forall v, eval v f = true.
Definition sat (G : list form) (v : nat -> bool) : Prop := forall f, In f G -> eval v f = true.

(* ---- Classically valid schemes --------------------------------------------- *)
Lemma lem_valid : forall n, valid (Or (FVar n) (Neg (FVar n))).
Proof. intros n v. simpl. destruct (v n); reflexivity. Qed.

Lemma dni_valid : forall f, valid (Imp f (Neg (Neg f))).
Proof. intros f v. simpl. destruct (eval v f); reflexivity. Qed.

Lemma dne_valid : forall f, valid (Imp (Neg (Neg f)) f).
Proof. intros f v. simpl. destruct (eval v f); reflexivity. Qed.

(* ---- Tableau closure soundness --------------------------------------------- *)
(* a formula and its negation cannot both be true *)
Lemma contra_no_model : forall f v, eval v f = true -> eval v (Neg f) = true -> False.
Proof. intros f v Hf Hnf. simpl in Hnf. rewrite Hf in Hnf. simpl in Hnf. discriminate. Qed.

(* a concrete unsatisfiable conjunction *)
Lemma and_neg_unsat : forall n v, eval v (And (FVar n) (Neg (FVar n))) = false.
Proof. intros n v. simpl. destruct (v n); reflexivity. Qed.

(* a CLOSED branch (contains some f and ~f) has no model -- tableau soundness core *)
Definition closed (G : list form) : Prop := exists f, In f G /\ In (Neg f) G.

Lemma closed_unsat : forall G, closed G -> forall v, ~ sat G v.
Proof.
  intros G [f [Hf Hnf]] v Hsat.
  apply (contra_no_model f v).
  - apply Hsat; exact Hf.
  - apply Hsat; exact Hnf.
Qed.

(* ---- NEGATIVE : `And` is binary -------------------------------------------- *)
Fail Definition bad_form : form := And (FVar 0).
