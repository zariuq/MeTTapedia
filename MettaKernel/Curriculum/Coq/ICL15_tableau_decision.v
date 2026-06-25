(* ============================================================================
   ICL Ch.11 — a VERIFIED decision procedure for propositional validity
   (MeTTaKernel curriculum, DTT ladder, Coq).  Exhaustive enumeration of the
   valuations over the variables of a formula = the semantic tableau closing
   every branch.  This file: semantics + the "eval depends only on the occurring
   variables" lemma; the decision procedure + its soundness/completeness follow.
   ========================================================================== *)

From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Inductive form : Type := Var (n : nat) | Bot | Imp (a b : form).

Fixpoint eval (v : nat -> bool) (f : form) : bool :=
  match f with
  | Var n   => v n
  | Bot     => false
  | Imp a b => implb (eval v a) (eval v b)
  end.

Fixpoint vars (a : form) : list nat :=
  match a with Var n => [n] | Bot => [] | Imp a b => vars a ++ vars b end.

(* ---- eval depends only on the variables that occur ------------------------- *)
Lemma eval_ext : forall a v v',
  (forall n, In n (vars a) -> v n = v' n) -> eval v a = eval v' a.
Proof.
  induction a as [n | | a IHa b IHb]; intros v v' Hag; simpl.
  - apply Hag. simpl. left. reflexivity.
  - reflexivity.
  - rewrite (IHa v v'). rewrite (IHb v v'). reflexivity.
    + intros n Hn. apply Hag. simpl. apply in_or_app. right. exact Hn.
    + intros n Hn. apply Hag. simpl. apply in_or_app. left. exact Hn.
Qed.

(* ---- enumerate every valuation over a list of variables -------------------- *)
Definition setv (v : nat -> bool) (n : nat) (b : bool) : nat -> bool :=
  fun m => if Nat.eqb n m then b else v m.

Fixpoint allAssign (L : list nat) (v0 : nat -> bool) : list (nat -> bool) :=
  match L with
  | [] => [v0]
  | n :: L' => let rest := allAssign L' v0 in
               map (fun v => setv v n true) rest ++ map (fun v => setv v n false) rest
  end.

Definition decide_valid (a : form) : bool :=
  forallb (fun v => eval v a) (allAssign (vars a) (fun _ => false)).

(* computational sanity (executed, not yet proved-correct): *)
(* a -> a is valid; a alone is not *)
Example dec_taut : decide_valid (Imp (Var 0) (Var 0)) = true := eq_refl.
Example dec_nontaut : decide_valid (Var 0) = false := eq_refl.
(* Peirce's law: classically valid (intuitionistically NOT) -- the procedure confirms validity *)
Example dec_peirce : decide_valid (Imp (Imp (Imp (Var 0) (Var 1)) (Var 0)) (Var 0)) = true := eq_refl.

(* ---- the enumeration meets every valuation on the occurring variables ------ *)
Lemma allAssign_complete : forall L v0 v,
  exists w, In w (allAssign L v0) /\ (forall n, In n L -> w n = v n).
Proof.
  induction L as [| k L IH]; intros v0 v; simpl.
  - exists v0. split. + left; reflexivity. + intros m H; destruct H.
  - destruct (IH v0 v) as [w0 [Hin Hag]]. destruct (v k) eqn:Evk.
    + exists (setv w0 k true). split.
      * apply in_or_app. left. apply in_map_iff. exists w0. split. reflexivity. exact Hin.
      * intros m Hm. unfold setv. destruct (Nat.eqb k m) eqn:Ekm.
        -- apply Nat.eqb_eq in Ekm. subst. symmetry. exact Evk.
        -- destruct Hm as [Hm | Hm].
           ++ subst m. rewrite Nat.eqb_refl in Ekm. discriminate.
           ++ apply Hag. exact Hm.
    + exists (setv w0 k false). split.
      * apply in_or_app. right. apply in_map_iff. exists w0. split. reflexivity. exact Hin.
      * intros m Hm. unfold setv. destruct (Nat.eqb k m) eqn:Ekm.
        -- apply Nat.eqb_eq in Ekm. subst. symmetry. exact Evk.
        -- destruct Hm as [Hm | Hm].
           ++ subst m. rewrite Nat.eqb_refl in Ekm. discriminate.
           ++ apply Hag. exact Hm.
Qed.

(* ---- DECISION PROCEDURE soundness + completeness w.r.t. the semantics ------ *)
Theorem decide_valid_correct : forall a, decide_valid a = true <-> (forall v, eval v a = true).
Proof.
  intros a. unfold decide_valid. split.
  - intros Hdec v. rewrite forallb_forall in Hdec.
    destruct (allAssign_complete (vars a) (fun _ => false) v) as [w [Hin Hag]].
    rewrite (eval_ext a v w).
    + apply Hdec. exact Hin.
    + intros n Hn. symmetry. apply Hag. exact Hn.
  - intro H. rewrite forallb_forall. intros w Hw. apply H.
Qed.

(* NEGATIVE: Var 0 is NOT valid -- the decision procedure returns false, not true *)
Fail Example neg_var_valid : decide_valid (Var 0) = true := eq_refl.
