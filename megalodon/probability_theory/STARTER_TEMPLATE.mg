(* Probability Theory: Sigma Algebras - STARTER TEMPLATE
   Based on Billingsley "Probability and Measure" Chapter 1, Section 2

   DELETE THIS HEADER ONCE YOU START WORKING!

   This is a template to help you get started.
   Replace the admits with real proofs as you go.
*)

Title "Sigma Algebras for Probability Theory".
Author "Gemini (guided by Billingsley)".

(* ===== STEP 1: Check what's in the preamble ===== *)

(* The Egal preamble already defines:
   - Empty : set (empty set)
   - Power : set -> set (power set)
   - Union : set -> set (union of a set of sets)
   - In : set -> set -> prop (membership, written x :e X)
   - Subq : set -> set -> prop (subset, written A c= B)
   - setminus : MIGHT exist, check!

   Use grep to search:
   grep "Definition setminus" /home/zar/.../PfgEAug2022Preamble.mgs
*)

(* ===== STEP 2: Define helper operations ===== *)

(* Set difference: Ω \ A *)
Definition setminus : set -> set -> set :=
  fun Omega A => {x :e Omega | ~(x :e A)}.

(* Binary union: A ∪ B *)
Definition setunion : set -> set -> set :=
  fun A B => {x | x :e A \/ x :e B}.

(* Binary intersection: A ∩ B *)
Definition setinter : set -> set -> set :=
  fun A B => {x | x :e A /\ x :e B}.

(* Disjoint sets *)
Definition Disjoint : set -> set -> prop :=
  fun A B => forall x, ~(x :e A /\ x :e B).

(* Pairwise disjoint family *)
Definition pairwise_disjoint : (set -> set) -> prop :=
  fun f => forall m n :e omega, m <> n -> Disjoint (f m) (f n).

(* CHALLENGE: Countable union ⋃ₙ f(n)
   Option 1: Use Union from preamble with image of f
   Option 2: Define directly

   Try this first:
*)
Definition bigcup_nat : (set -> set) -> set :=
  fun f => Union {f n | n :e omega}.
  (* This creates the set {f(0), f(1), f(2), ...} then takes its union *)

(* ===== STEP 3: Define field ===== *)

Definition is_field : set -> (set -> set -> prop) -> prop :=
  fun Omega In =>
    Omega :e In                                         (* Ω is in the field *)
    /\ Empty :e In                                       (* ∅ is in the field *)
    /\ (forall A, A :e In -> (setminus Omega A) :e In)  (* Closed under complement *)
    /\ (forall A B, A :e In -> B :e In -> (setunion A B) :e In). (* Closed under finite union *)

(* ===== STEP 4: First theorem - try to prove! ===== *)

Theorem field_has_omega :
  forall Omega In, is_field Omega In -> Omega :e In.
(* This should be trivial - it's literally in the definition! *)
assume Omega In.
assume H: is_field Omega In.
prove Omega :e In.
apply H.  (* Deconstruct the /\ conjunction *)
assume H1: Omega :e In.
assume H2: Empty :e In.
assume H3: forall A, A :e In -> (setminus Omega A) :e In.
assume H4: forall A B, A :e In -> B :e In -> (setunion A B) :e In.
exact H1.  (* Goal is Omega :e In, which is H1 *)
Qed.

(* ===== STEP 5: Prove fields are closed under intersection ===== *)

Theorem field_closed_under_intersection :
  forall Omega In A B,
    is_field Omega In ->
    A :e In -> B :e In ->
    (setinter A B) :e In.
(* Proof sketch from Billingsley:
   A ∩ B = ((Aᶜ ∪ Bᶜ)ᶜ) by DeMorgan's law
   Since A, B ∈ F, we have Aᶜ, Bᶜ ∈ F (complement closure)
   Then Aᶜ ∪ Bᶜ ∈ F (union closure)
   Then (Aᶜ ∪ Bᶜ)ᶜ ∈ F (complement closure)

   Steps:
   1. Use field_def to get complement closure
   2. Use field_def to get union closure
   3. Use complement closure again
   4. Show setinter A B = setminus Omega (setunion (setminus Omega A) (setminus Omega B))
*)
admit.  (* TODO: Prove this! Break it into smaller steps if needed *)
Qed.

(* ===== STEP 6: Define σ-field ===== *)

Definition is_sigma_field : set -> (set -> set -> prop) -> prop :=
  fun Omega In =>
    is_field Omega In
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e In) ->
         bigcup_nat f :e In).

(* ===== STEP 7: Try proving σ-fields are fields ===== *)

Theorem sigma_field_is_field :
  forall Omega In,
    is_sigma_field Omega In ->
    is_field Omega In.
assume Omega In.
assume H: is_sigma_field Omega In.
prove is_field Omega In.
apply H.  (* Deconstruct is_sigma_field *)
assume H1: is_field Omega In.
assume H2: forall f : set -> set, (forall n :e omega, f n :e In) -> bigcup_nat f :e In.
exact H1.  (* Goal is is_field Omega In, which is H1 *)
Qed.

(* ===== NEXT STEPS ===== *)

(* Now you should:
   1. Verify this file compiles
   2. Prove field_closed_under_intersection
   3. Add more theorems:
      - field_closed_under_finite_union (n sets)
      - sigma_field_closed_under_countable_intersection
      - DeMorgan's laws
   4. Add examples (power set is a σ-field, etc.)
   5. Update PROGRESS.md
*)

(* ===== EXAMPLE to add later ===== *)

(* Example: The power set is a σ-field *)
(* Theorem power_set_is_sigma_field :
  forall Omega,
    is_sigma_field Omega (fun A => A c= Omega).
... prove ...
Qed. *)
