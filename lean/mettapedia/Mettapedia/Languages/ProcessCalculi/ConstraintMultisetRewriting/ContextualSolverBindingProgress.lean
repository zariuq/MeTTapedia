import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPatternImages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure

/-!
# Progress and fragment preservation of a located binding choice

The equation's exact prefix and suffix are retained by `Choice.perform`.
Its actual queue agrees with the binding selection's mapped queue, so the
existing model factorization, strict active-image decrease and fragment
preservation apply to the same executable operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverBindingProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualPatternFragment
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

def choice {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source) :
    Choice (before ++ (observe left, observe right) :: after) :=
  ⟨before, _, .binding binding, after, rfl⟩

def selection {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source) :
    ContextualBindingWorklist.Selection (before ++ (observe left, observe right) :: after) :=
  ⟨Γ, sort, left, right, binding, before, after, rfl⟩

theorem same_remaining {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source) :
    (choice binding before after).perform.remaining = (selection binding before after).update.remaining := by
  dsimp only [choice, selection, Choice.perform, RootCase.perform,
    ContextualFrameUpdate.Update.keep_left, ContextualFrameUpdate.Update.keep_right,
    ContextualBindingWorklist.Selection.update]
  rw [ContextualProblemMapping.append]
  rfl

theorem model_progress {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source)
    (candidate : Assignment source next) (solved : Models candidate (before ++ (observe left, observe right) :: after)) :
    Models candidate (choice binding before after).perform.remaining ∧
      (∀ identity, candidate identity = instantiate candidate ((choice binding before after).perform.answer identity)) ∧
      Smaller (measure candidate (choice binding before after).perform.remaining)
        (measure candidate (before ++ (observe left, observe right) :: after)) := by
  have progressed := ContextualBindingSelectionProgress.model_progress (selection binding before after) candidate solved
  refine ⟨?_, progressed.2.1, ?_⟩
  · rw [same_remaining]
    exact progressed.1
  · apply of_image_lt
    dsimp only [ContextualSolverMeasure.measure]
    rw [same_remaining]
    exact progressed.2.2

theorem preserves_patterns {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
    (binding : ContextualBindingCase.Case left right) (before after : Problem source)
    (patterned : ProblemPattern (before ++ (observe left, observe right) :: after)) :
    ProblemPattern (choice binding before after).perform.remaining := by
  rw [same_remaining]
  exact ContextualBindingPatternImages.selection_preserves (selection binding before after) patterned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverBindingProgress
