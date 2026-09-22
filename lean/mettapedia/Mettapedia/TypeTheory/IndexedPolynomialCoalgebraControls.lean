import Mettapedia.TypeTheory.IndexedPolynomialCoalgebra

/-!
# Indexed provider prefixes and retained obligations

The provider realizes an arithmetic method inventory with independently typed
child goals and certified literal leaves. Its local state records an age tag
that advances differently at the two premise occurrences. Exact prefix trees
retain those tags, while completed arithmetic reconstruction does not depend
on them. A coalgebra morphism shifts the tags and preserves every prefix.

A depth boundary leaves actual provider states in the tree. It is not a
refutation or a global search-exhaustion result. No such result carrier is
introduced by the prefix operation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.CoalgebraicPlans.Controls

open CategoryTheory

inductive Expression where
  | literal (value : Nat)
  | add (left right : Expression)
deriving DecidableEq, Repr

def value : Expression → Nat
  | .literal number => number
  | .add left right => value left + value right

/-- Returned values carry a certificate of the actual indexed computation. -/
abbrev Answer (expression : Expression) := {number : Nat // number = value expression}

inductive Method : Expression → Type where
  | add (left right : Expression) : Method (.add left right)

abbrev methods : IndexedPolynomial Unit (fun _ => Expression) where
  Shape := fun _ expression => Method expression
  Position := fun _ => Bool
  next := fun method premise => match method with
    | .add left right => if premise then right else left

/-- The original method reconstructs a certified sum from both child answers. -/
def reconstruction : methods.Algebra (fun _ expression => Answer expression) where
  act := fun _ _ layer => by
    obtain ⟨method, children⟩ := layer
    cases method with
    | add left right =>
        exact ⟨(children false).val + (children true).val, by
          change (children false).val + (children true).val = value left + value right
          rw [(children false).property, (children true).property]
          rfl⟩

/-- An actual provider exposes certified leaves or the two indexed child states. -/
abbrev provider : Realizer (P := methods) (H := fun _ expression => Answer expression) where
  V := fun _ _ => Nat
  str := fun _ expression => ↾(fun age =>
    match expression with
    | .literal number => ⟨.inl ⟨number, rfl⟩, fun position => position.elim⟩
    | .add left right =>
        ⟨.inr (.add left right), fun (premise : Bool) =>
          if premise then age + 2 else age + 1⟩)

def sumGoal : Expression := .add (.literal 3) (.literal 5)

def pending : methods.Free (Residual provider) () sumGoal :=
  Free.node methods (.add (.literal 3) (.literal 5)) (fun premise =>
    Free.pure methods (.inl (if premise then 9 else 8)))

def completed : methods.Free (Residual provider) () sumGoal :=
  Free.node methods (.add (.literal 3) (.literal 5)) (fun premise =>
    match premise with
    | true => Free.pure methods (.inr ⟨5, rfl⟩)
    | false => Free.pure methods (.inr ⟨3, rfl⟩))

theorem one_layer_retains_both_actual_child_states :
    unfoldPrefix provider 1 () sumGoal 7 = pending := by
  rfl

theorem two_layers_return_different_certified_children :
    unfoldPrefix provider 2 () sumGoal 7 = completed := by
  change Free.node methods (.add (.literal 3) (.literal 5))
      (fun (premise : Bool) => unfoldPrefix provider 1 ()
        (if premise then .literal 5 else .literal 3) (if premise then 9 else 8)) =
    Free.node methods (.add (.literal 3) (.literal 5)) _
  apply congrArg (Free.node methods (.add (.literal 3) (.literal 5)))
  funext premise
  cases premise <;> rfl

theorem actual_resumption_equals_the_completed_tree :
    Free.bind methods (resume provider 1) () sumGoal pending = completed := by
  rw [← one_layer_retains_both_actual_child_states, ← prefix_add]
  exact two_layers_return_different_certified_children

/-- A depth cut retains an unfinished state, not a fabricated answer. -/
theorem zero_depth_cannot_return_a_certificate
    (answer : Answer sumGoal) :
    unfoldPrefix provider 0 () sumGoal 7 ≠ Free.pure methods (.inr answer) := by
  intro equal
  have shapes := congrArg
    (fun tree => (Fix.out (methods.withHoles (Residual provider)) tree).1) equal
  cases shapes

theorem different_pending_states_are_not_equal :
    unfoldPrefix provider 0 () sumGoal 7 ≠ unfoldPrefix provider 0 () sumGoal 8 := by
  intro equal
  have shapes := congrArg
    (fun tree => (Fix.out (methods.withHoles (Residual provider)) tree).1) equal
  cases shapes

/-- Returned leaves have no additional provider transition during resumption. -/
theorem returned_certificate_is_retained (depth : Nat) :
    resume provider depth () (.literal 3) (.inr ⟨3, rfl⟩) =
      Free.pure methods (.inr ⟨3, rfl⟩) := rfl

/-- Changing the age representation is a lawful coalgebra map, not a change
to which method is chosen or what arithmetic evidence is returned. -/
def shift (amount : Nat) : provider ⟶ provider where
  f := fun _ _ => ↾(fun age => age + amount)
  h := by
    funext base expression
    apply ConcreteCategory.hom_ext
    intro age
    cases expression with
    | literal number =>
        change (⟨.inl ⟨number, rfl⟩, fun position =>
          (position.elim : Nat) + amount⟩ :
          (methods.withHoles (fun _ expression => Answer expression)).Extension
            provider.V base (.literal number)) =
          ⟨.inl ⟨number, rfl⟩, fun position => position.elim⟩
        congr 1
        funext position
        exact position.elim
    | add left right =>
        change (⟨.inr (.add left right), fun (premise : Bool) =>
          (if premise then age + 2 else age + 1) + amount⟩ :
          (methods.withHoles (fun _ expression => Answer expression)).Extension
            provider.V base (.add left right)) =
          ⟨.inr (.add left right), fun (premise : Bool) =>
            if premise then age + amount + 2 else age + amount + 1⟩
        congr 1
        funext premise
        cases premise <;> simp [Nat.add_assoc, Nat.add_comm]

theorem actual_state_shift_preserves_every_prefix (amount depth : Nat)
    (expression : Expression) (age : Nat) :
    Free.map methods (residualMap (shift amount)) () expression
        (unfoldPrefix provider depth () expression age) =
      unfoldPrefix provider depth () expression (age + amount) :=
  prefix_hom (shift amount) depth age

/-- Supplying unresolved leaves as absent answers keeps reconstruction open. -/
noncomputable def partialAnswers : methods.Algebra
    (fun _ expression => Option (Answer expression)) where
  act := fun _ _ layer => by
    obtain ⟨method, children⟩ := layer
    cases method with
    | add left right => exact do
        let leftAnswer ← children false
        let rightAnswer ← children true
        pure ⟨leftAnswer.val + rightAnswer.val, by
          change leftAnswer.val + rightAnswer.val = value left + value right
          rw [leftAnswer.property, rightAnswer.property]
          rfl⟩

def leafAnswer : ∀ base expression, Residual provider base expression → Option (Answer expression)
  | _, _, .inl _ => none
  | _, _, .inr answer => some answer

theorem pending_reconstruction_is_unresolved :
    Free.fold methods leafAnswer partialAnswers () sumGoal pending = none := rfl

theorem completed_reconstruction_is_the_certified_sum :
    (Free.fold methods leafAnswer partialAnswers () sumGoal completed).map Subtype.val =
      some 8 := rfl

theorem another_number_cannot_be_an_answer :
    ¬ ∃ answer : Answer sumGoal, answer.val = 9 := by
  rintro ⟨answer, wrong⟩
  have correct := answer.property
  rw [wrong] at correct
  contradiction

end Mettapedia.TypeTheory.IndexedPolynomial.CoalgebraicPlans.Controls
