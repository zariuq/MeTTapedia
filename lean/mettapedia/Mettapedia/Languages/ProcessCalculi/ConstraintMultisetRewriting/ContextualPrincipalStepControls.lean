import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswerControls

/-!
# A fresh helper cannot justify an unrelated contextual frame guard

The principal contextual answer introduces a helper over the common scope of
two selected holes. Its retained interface also includes the surviving frame
and the proposed constant. Transporting the actual occurrence firing therefore
rejects the invented frame guard, both before and after solving.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalStep.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ScopePullback.Controls (base leftMap rightMap pullback)
open ContextualFlexPair.Controls (others)
open ContextualFreshAnswer.Controls
  (context old active A σ leftCall rightCall oldFrame frame output label initial selected rule
    constant unjustifiedRule ordinary_step_is_valid a_frame_guard_cannot_be_invented)

def oldConstant : Term (signature base old) context () := .op (.inl .constant) .nil
def observed := [leftCall, rightCall, frame, constant]

theorem the_retained_interface_covers_the_unrelated_guard :
    A.PrincipalOn (selected.problem label unjustifiedRule initial) σ observed :=
  ContextualFreshAnswer.principal_on pullback () others
    [ContextualFreshAnswer.originalLeft (left := leftMap) () others,
      ContextualFreshAnswer.originalRight (right := rightMap) () others, oldFrame, oldConstant]

theorem all_guard_arguments_are_retained :
    ∀ check ∈ unjustifiedRule.checks, ∀ term ∈ check.terms, term ∈ observed := by
  intro check member term inTerms
  change check ∈ [Check.equal frame constant] at member
  have only := List.mem_singleton.mp member
  subst check
  change term ∈ [frame, constant] at inTerms
  have choices : term = frame ∨ term = constant := by simpa using inTerms
  rcases choices with rfl | rfl <;> simp [observed]

theorem all_surviving_world_values_are_retained :
    ∀ occurrence ∈ initial.present, label occurrence ∈ observed := by
  intro occurrence member
  have choices : occurrence = 0 ∨ occurrence = 1 := by simpa [initial] using member
  rcases choices with rfl | rfl <;> simp [label, observed]

theorem the_transformed_firing_still_rejects_the_invented_frame_guard :
    ¬ selected.Valid A (fun occurrence => A.apply σ (label occurrence))
      (unjustifiedRule.map (A.apply σ)) (SubstitutionStability.configuration A σ initial) := by
  intro valid
  apply a_frame_guard_cannot_be_invented
  apply (PrincipalStep.valid_iff A label (rule := unjustifiedRule)
    the_retained_interface_covers_the_unrelated_guard ?_ ordinary_step_is_valid.occurrences
      all_guard_arguments_are_retained all_surviving_world_values_are_retained).mpr valid
  exact ⟨ordinary_step_is_valid.take_distinct, ordinary_step_is_valid.output_distinct,
    ordinary_step_is_valid.take_length, ordinary_step_is_valid.read_length, ordinary_step_is_valid.outputs⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalStep.Controls
