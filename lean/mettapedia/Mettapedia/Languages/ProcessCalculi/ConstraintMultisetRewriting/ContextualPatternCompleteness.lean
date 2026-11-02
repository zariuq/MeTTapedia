import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverPatternAvailability

/-!
# Every supplied solvable structural pattern problem finishes in the actual driver

Model-guided finite saturation returns a rigid-normal residual. The driver
preserves structural patterns, and a nonempty modelled residual in that
fragment always has an implemented choice. Thus the actual returned queue
is empty and its computed assignment solves the original equations. Every
other model factors through that same answer, including models in later
declaration families. No finiteness of the ambient family is required.

This theorem concerns supplied solvable structural pattern problems. General
applications may retain residual equations, and termination on arbitrary
unsatisfiable inputs is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternCompleteness

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualFrameUpdate

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

theorem solves_of_model {Next : Type} (next : Next → MetaArity S) (problem : Problem source)
    (patterned : ProblemPattern problem) (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      ContextualFrameWorklist.run fuel source problem = .residual update ∧
        update.remaining = [] ∧ Models update.answer problem := by
  obtain ⟨fuel, update, computed, saturated, normal⟩ :=
    ContextualFrameSaturation.saturates_normalized next problem candidate solved
  let _ := update.equality
  have remainingPattern := ContextualSolverPatterns.run_preserves fuel source problem patterned computed
  obtain ⟨residual, residualSolved, _⟩ := update.valid.complete next candidate solved
  have empty := ContextualSolverPatternAvailability.normal_pattern_saturated_empty update.remaining normal
    remainingPattern residual residualSolved saturated
  exact ⟨fuel, update, computed, empty, update.completed empty⟩

theorem solves_principally_of_model {Next : Type} (next : Next → MetaArity S) (problem : Problem source)
    (patterned : ProblemPattern problem) (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      ContextualFrameWorklist.run fuel source problem = .residual update ∧
        update.remaining = [] ∧ Models update.answer problem ∧
        ∀ {Later : Type} (later : Later → MetaArity S) (other : Assignment source later), Models other problem →
          ∃ factor : Assignment update.declaration later,
            ∀ identity, other identity = instantiate factor (update.answer identity) := by
  obtain ⟨fuel, update, computed, empty, answer⟩ := solves_of_model next problem patterned candidate solved
  refine ⟨fuel, update, computed, empty, answer, ?_⟩
  intro Later later other models
  obtain ⟨factor, _, components⟩ := update.valid.complete later other models
  exact ⟨factor, components⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternCompleteness
