import Mathlib.Computability.StateTransition

/-!
# Composition of operational refinements

A relational simulation sends each source step to a nonempty finite target
path and preserves terminal states. These refinements compose, retaining the
intermediate-state witnesses. Mathlib's execution and termination transport
lemmas then apply to the composed relation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.StateTransition

/-- Relational refinements compose. Nonempty source-step simulations prevent
an infinite source computation from disappearing into zero target steps. -/
theorem respects_comp {A B C : Type*} {first : A → Option A}
    {second : B → Option B} {third : C → Option C}
    {left : A → B → Prop} {right : B → C → Prop}
    (firstRefinement : _root_.StateTransition.Respects first second left)
    (secondRefinement : _root_.StateTransition.Respects second third right) :
    _root_.StateTransition.Respects first third
      (fun source target => ∃ middle, left source middle ∧ right middle target) := by
  intro source target related
  obtain ⟨middle, leftRelated, rightRelated⟩ := related
  have firstStep := firstRefinement leftRelated
  cases stepped : first source with
  | none =>
      rw [stepped] at firstStep
      have secondStep := secondRefinement rightRelated
      rwa [firstStep] at secondStep
  | some next =>
      rw [stepped] at firstStep
      obtain ⟨middleNext, nextRelated, path⟩ := firstStep
      obtain ⟨targetNext, finalRelated, targetPath⟩ :=
        _root_.StateTransition.tr_reaches₁ secondRefinement rightRelated path
      exact ⟨targetNext, ⟨middleNext, nextRelated, finalRelated⟩, targetPath⟩

end Mettapedia.Computability.StateTransition
