import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingTermination
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklistControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupportControls

/-!
# Binding termination does not collapse residual syntax into a proof

Three widely separated names in an infinite declaration family finish in
four passes and produce a solution of the original equations. A repeated
spine stops with its equation retained; so does an unavailable capture in
this phase. A conflicting shared hole still returns a certified refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingTerminationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualBindingWorklist
open ContextualBindingTermination

abbrev base := ContextualBindingWorklist.Controls.base
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
abbrev source := ContextualActiveSupportControls.declaration
abbrev problem := ContextualActiveSupportControls.problem

def remainingCount {Names : Type} {declaration : Names → MetaArity base}
    {equations : Problem declaration} : ContextualBindingWorklist.Result equations → Option Nat
  | .residual update => some update.remaining.length
  | .refuted _ => none

theorem an_infinite_ambient_family_has_a_three_name_roster : (active problem).card = 3 := by
  decide +kernel

theorem its_binding_phase_has_the_computed_bound_four :
    ∃ fuel, fuel ≤ 4 ∧ Finished (run (S := base) (declaration := source) fuel problem) := by
  have stopped := stopping_bound (S := base) problem
  simpa only [an_infinite_ambient_family_has_a_three_name_roster] using stopped

theorem all_three_distant_names_are_solved_within_that_bound :
    remainingCount (run (S := base) (declaration := source) 4 problem) = some 0 := by
  decide +kernel

theorem that_computed_answer_solves_the_original_equations :
    ∃ update, run (S := base) (declaration := source) 4 problem = .residual update ∧
      update.remaining = [] ∧ Models update.answer problem := by
  have count := all_three_distant_names_are_solved_within_that_bound
  cases computed : run (S := base) (declaration := source) 4 problem with
  | refuted impossible => simp only [computed, remainingCount, reduceCtorEq] at count
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, remainingCount, Option.some.injEq, List.length_eq_zero_iff] using count
      exact ⟨update, rfl, empty, completed_sound update empty⟩

theorem stopping_can_leave_a_repeated_application_unresolved :
    remainingCount (run (S := base) 1 Controls.repeatedProblem) = some 1 := by
  decide +kernel

theorem stopping_does_not_admit_the_missing_ambient_variable :
    remainingCount (run (S := base) 1 Controls.captureProblem) = some 1 := by
  decide +kernel

theorem conflicting_shared_uses_still_refute :
    remainingCount (run (S := base) 3 Controls.conflictProblem) = none := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingTerminationControls
