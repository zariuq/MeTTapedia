import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverBindingProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverImitationProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverSelfProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverFlexProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverReflexiveProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemOrientation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

/-!
# Every retained solver choice strictly decreases its supplied model measure

The proof follows the concrete root case and its actual queue location.
Reversing an equation uses the proved constraint observation laws. No
progress hypothesis is added to the case data or supplied by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualSolverCases
open ContextualSolverMeasure

variable {S : Signature} {V Next : Type} [DecidableEq V] {source : V → MetaArity S}
  {next : Next → MetaArity S}

theorem root_progress {equation : Equation (Observation S source)} (selected : RootCase S source equation) :
    ∀ (before after : Problem source) (candidate : Assignment source next),
    Models candidate (before ++ equation :: after) →
    let update := (selected.locate before after).perform
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure candidate (before ++ equation :: after)) := by
  induction selected with
  | reflexive term =>
      intro before after candidate solved
      have progressed := ContextualSolverReflexiveProgress.model_progress term before after candidate solved
      exact ⟨candidate, progressed⟩
  | binding recovered =>
      intro before after candidate solved
      have progressed := ContextualSolverBindingProgress.model_progress recovered before after candidate solved
      exact ⟨candidate, progressed⟩
  | imitation identity rho operator fields =>
      exact ContextualSolverImitationProgress.model_progress identity rho operator fields
  | selfPair identity left right different =>
      exact ContextualSolverSelfProgress.model_progress identity left right different
  | flexPair first second different sorts left right =>
      exact ContextualSolverFlexProgress.model_progress first second different sorts left right
  | @reverse equation original smaller =>
      intro before after candidate solved
      have flipped := (ContextualProblemOrientation.models_at candidate equation before after).mp solved
      let _ := (original.locate before after).perform.equality
      obtain ⟨remaining, models, components, decrease⟩ := smaller before after candidate flipped
      refine ⟨remaining, models, components, ?_⟩
      exact Eq.mpr (congrArg (fun bound => Smaller (ContextualSolverMeasure.measure remaining
        (original.locate before after).perform.remaining) bound)
        (ContextualProblemOrientation.measure_at candidate equation before after)) decrease

theorem model_progress {problem : Problem source} (selected : Choice problem)
    (candidate : Assignment source next) (solved : Models candidate problem) :
    let update := selected.perform
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure candidate problem) := by
  rcases selected with ⟨before, equation, root, after, split⟩
  subst problem
  exact root_progress root before after candidate solved

theorem computed_progress [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem : Problem source} {update : ContextualFrameUpdate.Update problem}
    (computed : ContextualFrameWorklist.choose problem = some update)
    (candidate : Assignment source next) (solved : Models candidate problem) :
    letI := update.equality
    ∃ remaining : Assignment update.declaration next, Models remaining update.remaining ∧
      (∀ name, candidate name = instantiate remaining (update.answer name)) ∧
      Smaller (measure remaining update.remaining) (measure candidate problem) := by
  unfold ContextualFrameWorklist.choose at computed
  obtain ⟨selected, _, rfl⟩ := Option.map_eq_some_iff.mp computed
  exact model_progress selected candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverChoiceProgress
