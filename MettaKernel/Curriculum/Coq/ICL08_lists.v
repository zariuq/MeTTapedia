(* ============================================================================
   ICL Ch.8 — Lists (comprehensive)   (MeTTaKernel curriculum, DTT ladder, Coq)
   Recursion + induction over the standard polymorphic list: append, length,
   reverse, membership, and map laws.  POSITIVES check; NEGATIVE via `Fail`.
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ---- append ---------------------------------------------------------------- *)
Lemma app_nil_r' : forall A (l : list A), l ++ [] = l.
Proof. intros A l. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma app_assoc' : forall A (l k m : list A), (l ++ k) ++ m = l ++ (k ++ m).
Proof. intros A l k m. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma length_app' : forall A (l k : list A), length (l ++ k) = length l + length k.
Proof. intros A l k. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

(* ---- reverse --------------------------------------------------------------- *)
Fixpoint rev' {A} (l : list A) : list A :=
  match l with [] => [] | x :: l' => rev' l' ++ [x] end.

Lemma rev_app_distr' : forall A (l k : list A), rev' (l ++ k) = rev' k ++ rev' l.
Proof.
  intros A l k. induction l as [| x l IH]; simpl.
  - rewrite app_nil_r'. reflexivity.
  - rewrite IH. rewrite app_assoc'. reflexivity.
Qed.

Lemma rev_involutive' : forall A (l : list A), rev' (rev' l) = l.
Proof.
  intros A l. induction l as [| x l IH]; simpl.
  - reflexivity.
  - rewrite rev_app_distr'. rewrite IH. simpl. reflexivity.
Qed.

Lemma length_rev' : forall A (l : list A), length (rev' l) = length l.
Proof.
  intros A l. induction l as [| x l IH]; simpl.
  - reflexivity.
  - rewrite length_app'. rewrite IH. simpl. lia.
Qed.

(* ---- membership ------------------------------------------------------------ *)
Lemma in_app' : forall A (x : A) (l k : list A), In x (l ++ k) <-> In x l \/ In x k.
Proof. intros A x l k. induction l as [| y l IH]; simpl; tauto. Qed.

(* ---- map ------------------------------------------------------------------- *)
Lemma map_app' : forall A B (f : A -> B) (l k : list A), map f (l ++ k) = map f l ++ map f k.
Proof. intros A B f l k. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma length_map' : forall A B (f : A -> B) (l : list A), length (map f l) = length l.
Proof. intros A B f l. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma map_map' : forall A B C (f : A -> B) (g : B -> C) (l : list A),
  map g (map f l) = map (fun x => g (f x)) l.
Proof. intros A B C f g l. induction l as [| x l IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma in_map' : forall A B (f : A -> B) (l : list A) (x : A), In x l -> In (f x) (map f l).
Proof.
  intros A B f l x. induction l as [| y l IH]; simpl.
  - intro h. exact h.
  - intros [e | h]. + left. rewrite e. reflexivity. + right. apply IH. exact h.
Qed.

(* ---- fold (a concrete computation) ----------------------------------------- *)
Example fold_sum : fold_right Nat.add 0 [1; 2; 3] = 6 := eq_refl.

(* ---- NEGATIVE : a type-mismatched element is rejected ---------------------- *)
Fail Definition bad_list : list nat := true :: nil.
