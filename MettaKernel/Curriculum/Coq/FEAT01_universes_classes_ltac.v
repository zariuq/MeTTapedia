(* ============================================================================
   Coq FEATURE MIRROR 01 — universe polymorphism, type classes / instance
   resolution, and Ltac tactic-writing.  (MeTTaKernel curriculum; vanilla Rocq 9.1.)
   Mirrors, on the Coq side, kernel/proof-construction features the Lean ladder
   pins: universe polymorphism, instance resolution, and user-defined tactics.
   ========================================================================== *)

(* ---- Universe polymorphism : one definition usable at many universe levels - *)
Set Universe Polymorphism.

Definition idp {A : Type} (a : A) : A := a.
Definition use_small : nat := idp 3.       (* at a small type *)
Definition use_large : Type := idp nat.    (* at a large type *)

Polymorphic Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
Example compose_compute : compose S S 0 = 2 := eq_refl.

Unset Universe Polymorphism.

(* ---- Type classes + instance resolution ------------------------------------ *)
Class Eqb (A : Type) := { eqb : A -> A -> bool }.

Instance Eqb_nat  : Eqb nat  := { eqb := Nat.eqb }.
Instance Eqb_bool : Eqb bool := { eqb := fun a b : bool => if a then b else negb b }.

(* instance RESOLUTION: the method dispatches on the type automatically *)
Definition same {A : Type} `{Eqb A} (x y : A) : bool := eqb x y.
Example same_nat  : same 2 2 = true := eq_refl.
Example same_bool : same true false = false := eq_refl.

(* a polymorphic function over the class, plus a derived instance for pairs *)
Instance Eqb_prod {A B : Type} `{Eqb A} `{Eqb B} : Eqb (A * B) :=
  { eqb := fun p q => andb (eqb (fst p) (fst q)) (eqb (snd p) (snd q)) }.
Example same_pair : same (1, true) (1, true) = true := eq_refl.

(* ---- Ltac : a user-defined tactic ------------------------------------------ *)
Ltac crush := repeat (assumption || reflexivity || constructor || intro).

Lemma ltac_demo1 : forall P : Prop, P -> P. Proof. crush. Qed.
Lemma ltac_demo2 : True /\ (0 = 0).        Proof. crush. Qed.
Lemma ltac_demo3 : forall n : nat, n = n. Proof. crush. Qed.

(* ---- NEGATIVE : instance resolution fails when no instance exists ----------- *)
Fail Definition no_instance := same (fun x : nat => x) (fun x => x).
