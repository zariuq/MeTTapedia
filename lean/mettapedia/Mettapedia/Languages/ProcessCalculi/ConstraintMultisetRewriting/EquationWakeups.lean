import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders

/-!
# Readiness changes caused by equation refinement

The existing step appends port equations and tells even when its physical
commit changes no occurrence. These lemmas identify the resulting wakeup
obligation without adding a scheduler or a different transition relation.
Equation-list length is sufficient along an actual append-only step; it is
not claimed to identify arbitrary branches or contextual declaration families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeups

open GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

theorem step_refines (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before after : Configuration T O}
    (step : Step A label rule before after) :
    A.Refines after.equations before.equations := by
  obtain ⟨selection, _, rfl⟩ := step
  intro assignment solved
  rw [result_equations] at solved
  exact (A.models_append _ _ _).mp solved |>.1

theorem unchanged_length_keeps_equations (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    (sameLength : (selection.result label rule before).equations.length = before.equations.length) :
    (selection.result label rule before).equations = before.equations := by
  rw [result_equations] at sameLength ⊢
  have empty : added label rule selection = [] := by
    cases remaining : added label rule selection with
    | nil => rfl
    | cons head tail =>
      simp only [remaining, List.length_append, List.length_cons] at sameLength
      omega
  simp [empty]

theorem unchanged_step_length_keeps_equations (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before after : Configuration T O}
    (step : Step A label rule before after)
    (sameLength : after.equations.length = before.equations.length) :
    after.equations = before.equations := by
  obtain ⟨selection, _, rfl⟩ := step
  exact unchanged_length_keeps_equations label sameLength

theorem unchanged_step_preserves_readiness (A : SubstitutionAction T S) (label : O → T)
    {event pending : RuleInstance T} {before after : Configuration T O}
    (step : Step A label event before after)
    (sameWorld : before.present = after.present)
    (sameLength : after.equations.length = before.equations.length)
    (selection : Selection O) :
    selection.Valid A label pending before ↔ selection.Valid A label pending after := by
  have equations := unchanged_step_length_keeps_equations A label step sameLength
  apply valid_congr A label
  exact ⟨by rw [equations]; intro assignment; rfl, sameWorld⟩

theorem readiness_flip_requires_world_or_equations (A : SubstitutionAction T S) (label : O → T)
    {event pending : RuleInstance T} {before after : Configuration T O}
    (step : Step A label event before after) (selection : Selection O)
    (asleep : ¬ selection.Valid A label pending before)
    (awake : selection.Valid A label pending after) :
    before.present ≠ after.present ∨ before.equations.length ≠ after.equations.length := by
  classical
  by_cases world : before.present = after.present
  · right
    intro sameLength
    exact asleep ((unchanged_step_preserves_readiness A label step world sameLength.symm selection).mpr awake)
  · exact Or.inl world

theorem readiness_without_world_change_eliminates_model
    (A : SubstitutionAction T S) (label : O → T)
    {event pending : RuleInstance T} {before after : Configuration T O}
    (step : Step A label event before after) (selection : Selection O)
    (sameWorld : before.present = after.present)
    (asleep : ¬ selection.Valid A label pending before)
    (awake : selection.Valid A label pending after) :
    ∃ assignment, A.Models assignment before.equations ∧ ¬ A.Models assignment after.equations := by
  classical
  by_contra missing
  push Not at missing
  have equivalent : A.Equivalent before.equations after.equations := fun assignment =>
    ⟨missing assignment, step_refines A label step assignment⟩
  exact asleep ((valid_congr A label ⟨equivalent, sameWorld⟩).mpr awake)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeups
