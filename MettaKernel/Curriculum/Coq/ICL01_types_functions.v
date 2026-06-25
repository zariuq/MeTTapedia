(* ============================================================================
   ICL Ch.1 — Types and Functions   (MeTTaKernel curriculum, DTT ladder, Coq)
   Self-contained vanilla Rocq/Coq 9.1 (defines its own bool/nat/list, ICL-style).
   POSITIVES check with `coqc`; NEGATIVES are demonstrated inline with `Fail`
   (the file stays green precisely because the bad command is correctly rejected).
   ========================================================================== *)

(* ---- Booleans : an inductive type with two constructors --------------------- *)
Inductive bool : Type := true | false.

Definition negb (x : bool) : bool :=
  match x with true => false | false => true end.

Definition andb (x y : bool) : bool :=
  match x with true => y | false => false end.

Definition orb (x y : bool) : bool :=
  match x with true => true | false => y end.

(* case analysis + reflexivity *)
Lemma negb_negb : forall x, negb (negb x) = x.
Proof. destruct x; reflexivity. Qed.

Lemma andb_com : forall x y, andb x y = andb y x.
Proof. destruct x, y; reflexivity. Qed.

Lemma orb_com : forall x y, orb x y = orb y x.
Proof. destruct x, y; reflexivity. Qed.

(* NEGATIVE: a non-exhaustive match is rejected by the checker *)
Fail Definition bad_match (x : bool) : bool := match x with true => false end.
(* NEGATIVE: a value of the wrong type is rejected *)
Fail Definition bad_type : bool := negb.
(* NEGATIVE: over-application is rejected *)
Fail Definition over_app : bool := negb true true.

(* ---- Natural numbers : recursion + structural induction --------------------- *)
Inductive nat : Type := O | S (n : nat).

Fixpoint plus (x y : nat) : nat :=
  match x with O => y | S x' => S (plus x' y) end.

(* the two computation rules hold definitionally (by reflexivity) *)
Lemma plus_O_l : forall y, plus O y = y.
Proof. reflexivity. Qed.

Lemma plus_S_l : forall x y, plus (S x) y = S (plus x y).
Proof. reflexivity. Qed.

(* structural induction + rewriting with the inductive hypothesis *)
Lemma plus_O_r : forall x, plus x O = x.
Proof. induction x as [| x' IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma plus_assoc : forall x y z, plus (plus x y) z = plus x (plus y z).
Proof. intros x y z. induction x as [| x' IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

(* NEGATIVE: a non-structural (non-terminating) Fixpoint is rejected (guard checker) *)
Fail Fixpoint loop (n : nat) : nat := loop n.

(* ---- Pairs : a parametric inductive with one constructor -------------------- *)
Inductive prod (A B : Type) : Type := pair (a : A) (b : B).
Arguments pair {A B} a b.

Definition fst {A B} (p : prod A B) : A := match p with pair a _ => a end.
Definition snd {A B} (p : prod A B) : B := match p with pair _ b => b end.

Lemma surjective_pairing : forall A B (p : prod A B), p = pair (fst p) (snd p).
Proof. intros A B p. destruct p as [a b]. reflexivity. Qed.

(* ---- Lists : recursion over a parametric inductive -------------------------- *)
Inductive list (A : Type) : Type := nil | cons (a : A) (l : list A).
Arguments nil {A}.
Arguments cons {A} a l.

Fixpoint app {A} (l k : list A) : list A :=
  match l with nil => k | cons x l' => cons x (app l' k) end.

Fixpoint length {A} (l : list A) : nat :=
  match l with nil => O | cons _ l' => S (length l') end.

Lemma app_nil_r : forall A (l : list A), app l nil = l.
Proof. intros A l. induction l as [| x l' IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma app_assoc : forall A (l k m : list A), app (app l k) m = app l (app k m).
Proof. intros A l k m. induction l as [| x l' IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

Lemma length_app : forall A (l k : list A), length (app l k) = plus (length l) (length k).
Proof. intros A l k. induction l as [| x l' IH]; simpl. - reflexivity. - rewrite IH. reflexivity. Qed.

(* ---- Options : modelling partiality / finite cases -------------------------- *)
Inductive option (A : Type) : Type := Some (a : A) | None.
Arguments Some {A} a.
Arguments None {A}.

Definition head {A} (l : list A) : option A :=
  match l with nil => None | cons x _ => Some x end.

Lemma head_cons : forall A (x : A) l, head (cons x l) = Some x.
Proof. reflexivity. Qed.
