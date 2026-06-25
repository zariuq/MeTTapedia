(* ============================================================================
   ICL Ch.9 — Syntactic Unification   (MeTTaKernel curriculum, DTT ladder, Coq)
   First-order terms, substitutions as total maps, composition, unifiers, the
   occurs-check, and the "more general unifier" property.  POSITIVE / `Fail`.
   ========================================================================== *)

From Stdlib Require Import Bool.

(* ---- First-order terms: variables (nat), constants (nat), binary nodes ------ *)
Inductive term : Type :=
| Var (n : nat)
| Const (a : nat)
| Node (l r : term).

(* ---- Substitutions are total functions  var -> term ------------------------- *)
Definition subst := nat -> term.
Definition idsub : subst := fun n => Var n.

Fixpoint ap (s : subst) (t : term) : term :=
  match t with
  | Var n => s n
  | Const a => Const a
  | Node l r => Node (ap s l) (ap s r)
  end.

Lemma ap_id : forall t, ap idsub t = t.
Proof. induction t as [n | a | l IHl r IHr]; simpl. - reflexivity. - reflexivity. - rewrite IHl, IHr; reflexivity. Qed.

(* ---- Composition of substitutions ------------------------------------------ *)
Definition comp (s2 s1 : subst) : subst := fun n => ap s2 (s1 n).

Lemma ap_comp : forall s2 s1 t, ap (comp s2 s1) t = ap s2 (ap s1 t).
Proof. intros s2 s1 t. induction t as [n | a | l IHl r IHr]; simpl. - reflexivity. - reflexivity. - rewrite IHl, IHr; reflexivity. Qed.

(* ---- Unifiers -------------------------------------------------------------- *)
Definition unifies (s : subst) (t1 t2 : term) : Prop := ap s t1 = ap s t2.

(* a concrete unification:  Node (Var 0) (Const 1)  vs  Node (Const 1) (Var 0) *)
Definition s01 : subst := fun n => if Nat.eqb n 0 then Const 1 else Var n.
Example unify_example : unifies s01 (Node (Var 0) (Const 1)) (Node (Const 1) (Var 0)).
Proof. unfold unifies, s01. simpl. reflexivity. Qed.

(* any unifier stays a unifier after further substitution (the mgu property) *)
Lemma unifies_comp : forall s s' t1 t2, unifies s t1 t2 -> unifies (comp s' s) t1 t2.
Proof. intros s s' t1 t2 H. unfold unifies in *. rewrite !ap_comp. rewrite H. reflexivity. Qed.

(* ---- The occurs-check ------------------------------------------------------- *)
Fixpoint occurs (n : nat) (t : term) : bool :=
  match t with
  | Var m => Nat.eqb n m
  | Const _ => false
  | Node l r => orb (occurs n l) (occurs n r)
  end.

(* occurs-check soundness: if n does not occur in t, binding n leaves t fixed *)
Lemma occurs_false_ap : forall n u t, occurs n t = false ->
  ap (fun m => if Nat.eqb n m then u else Var m) t = t.
Proof.
  intros n u t H. induction t as [m | a | l IHl r IHr]; simpl in *.
  - destruct (Nat.eqb n m) eqn:E. + discriminate. + reflexivity.
  - reflexivity.
  - apply orb_false_iff in H. destruct H as [Hl Hr]. rewrite (IHl Hl), (IHr Hr). reflexivity.
Qed.

(* ---- NEGATIVE : a constant's label is a nat, not a term -------------------- *)
Fail Definition bad_term : term := Const (Var 0).
