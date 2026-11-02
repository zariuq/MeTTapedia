import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidNormalForm

/-!
# Finite saturation of the executable contextual frame worklist

Every supplied model gives a well-founded measure for the actual computed
choices. The induction allows the source declaration family to change when
fresh helpers are introduced, while keeping the model's target family fixed.
The resulting residual has no further implemented choice. General
applications may remain there, so this is not a completeness theorem for
arbitrary equations or a termination theorem on unsatisfiable inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameUpdate
open ContextualFrameWorklist
open ContextualSolverMeasure

variable {S : Signature} [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

private theorem saturation_by_measure {Next : Type} (next : Next → MetaArity S) (bound : Work) :
    ∀ {Names : Type} [DecidableEq Names] (declaration : Names → MetaArity S)
      (problem : Problem declaration) (candidate : Assignment declaration next),
      ContextualSolverMeasure.measure candidate problem = bound → Models candidate problem →
      ∃ (fuel : Nat) (update : Update problem),
        run fuel declaration problem = .residual update ∧
          (letI := update.equality
           choose (S := S) (source := update.declaration) update.remaining = none) ∧
          ContextualRigidNormalForm.ProblemNormal update.remaining := by
  induction bound using ContextualSolverMeasure.wellFounded.induction with
  | h bound earlier =>
      intro Names equality declaration problem candidate measured solved
      cases normalized : ContextualRigidSolver.normalize (S := S) (source := declaration) problem with
      | none =>
          exact False.elim (ContextualRigidSolver.refused_has_no_solution normalized candidate solved)
      | some remaining =>
          have remainingSolved : Models candidate remaining := by
            have equivalent := ContextualRigidSolver.models_normalize candidate problem
            rw [normalized] at equivalent
            exact equivalent.mpr solved
          have noRefutation : ContextualFrameRefutation.choose remaining = none := by
            cases refused : ContextualFrameRefutation.choose remaining with
            | none => rfl
            | some impossible => exact False.elim (impossible.noModel next candidate remainingSolved)
          let normalizedUpdate : Update problem :=
            ⟨Names, equality, declaration, generator declaration, remaining,
              ContextualRigidSolver.normalization_reduction normalized⟩
          cases selected : choose (S := S) (source := declaration) remaining with
          | none =>
              refine ⟨1, normalizedUpdate, ?_, selected,
                ContextualRigidNormalForm.normalization_normal problem normalized⟩
              simp only [run, runWithRefuter, normalizationUpdate]
              split
              · rename_i computed
                cases normalized.symm.trans computed
              · rename_i rest computed
                have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
                subst rest
                split
                · rename_i impossible computed
                  cases noRefutation.symm.trans computed
                · split
                  · rfl
                  · rename_i update computed
                    cases selected.symm.trans computed
          | some update =>
              let _ := update.equality
              obtain ⟨residual, residualSolved, _, decrease⟩ :=
                ContextualSolverChoiceProgress.computed_progress selected candidate remainingSolved
              have smaller : Smaller (ContextualSolverMeasure.measure residual update.remaining) bound := by
                rw [← measured]
                exact smaller_after_normalization normalized candidate decrease
              obtain ⟨fuel, last, finished, noChoice, normal⟩ :=
                earlier _ smaller update.declaration update.remaining residual rfl residualSolved
              refine ⟨fuel + 1, (normalizedUpdate.then update).then last, ?_, noChoice, normal⟩
              simp only [run, runWithRefuter, normalizationUpdate]
              split
              · rename_i computed
                cases normalized.symm.trans computed
              · rename_i rest computed
                have same : rest = remaining := Option.some.inj (computed.symm.trans normalized)
                subst rest
                split
                · rename_i impossible computed
                  cases noRefutation.symm.trans computed
                · split
                  · rename_i computed
                    cases selected.symm.trans computed
                  · rename_i chosen computed
                    have same : chosen = update := Option.some.inj (computed.symm.trans selected)
                    subst chosen
                    dsimp only [ContextualFrameUpdate.Update.then]
                    simp only [run] at finished
                    rw [finished]
                    rfl

variable {V : Type} [DecidableEq V] {source : V → MetaArity S}

/-- The finite saturated residual is an actual rigid-normalization output:
its equations have matching metadata and at least one flexible root. -/
theorem saturates_normalized {Next : Type} (next : Next → MetaArity S) (problem : Problem source)
    (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      run fuel source problem = .residual update ∧
        (letI := update.equality
         choose (S := S) (source := update.declaration) update.remaining = none) ∧
        ContextualRigidNormalForm.ProblemNormal update.remaining :=
  saturation_by_measure next _ source problem candidate rfl solved

/-- A model of the supplied problem guarantees a finite actual run ending
at a residual on which the implemented selector has no further choice. -/
theorem saturates {Next : Type} (next : Next → MetaArity S) (problem : Problem source)
    (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      run fuel source problem = .residual update ∧
        letI := update.equality
        choose (S := S) (source := update.declaration) update.remaining = none := by
  obtain ⟨fuel, update, computed, noChoice, _⟩ := saturates_normalized next problem candidate solved
  exact ⟨fuel, update, computed, noChoice⟩

/-- Saturation retains the original supplied model by factorization through
the assignment actually returned by the executable driver. -/
theorem saturates_preserving_every_solution {Next : Type} (next : Next → MetaArity S)
    (problem : Problem source) (candidate : Assignment source next) (solved : Models candidate problem) :
    ∃ (fuel : Nat) (update : Update problem),
      run fuel source problem = .residual update ∧
        (letI := update.equality
         choose (S := S) (source := update.declaration) update.remaining = none) ∧
        ∃ residual : Assignment update.declaration next, Models residual update.remaining ∧
          ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  obtain ⟨fuel, update, computed, noChoice⟩ := saturates next problem candidate solved
  exact ⟨fuel, update, computed, noChoice, update.valid.complete next candidate solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameSaturation
