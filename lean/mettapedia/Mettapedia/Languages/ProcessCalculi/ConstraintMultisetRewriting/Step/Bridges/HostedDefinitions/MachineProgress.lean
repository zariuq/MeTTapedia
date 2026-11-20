import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionInvariant
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramProgress

/-!
# The actual closed compiled machine adds no divergence to a normalizing input

Search descends through finite literal data; plugging removes finite frames;
substitution and value recognition use their checked terminating episodes.
Returning to evaluation requires an actual directed source reduction. The
outer well-founded induction therefore permits helper ranks to reset after
real computation without silently assuming a global scalar rank.

This theorem concerns closed equation rewriting. Lifting it to symbolic live
source branches requires their ground-determination and administrative laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextStack
open ContextProgress (Terminates)
open ExecutionInvariant (nextContinuation plugContinuation)

theorem resume_eval {dev : Definitions.Development} (built : Compiled dev) (term : Tower.Tm 0)
    (next : Terminates built (evaluateC (encodeTm term) finishContinuation)) :
    Terminates built (resumeC (encodeTm term) nextContinuation) := by
  refine .intro _ ?_
  intro after moved
  have same := MainReadback.resume_eval_step built (encodeTm term) finishContinuation after moved
  exact same.symm ▸ next

theorem resume_plug {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (term : Tower.Tm n) (stack : Stack 0 n)
    (next : Terminates built (plugC (encodeTm term) (code stack) nextContinuation)) :
    Terminates built (resumeC (encodeTm term) (plugContinuation stack)) := by
  refine .intro _ ?_
  intro after moved
  have same := MainReadback.resume_plug_step built (encodeTm term) (code stack) nextContinuation after moved
  exact same.symm ▸ next

theorem root {dev : Definitions.Development} (built : Compiled dev) (whole : Tower.Tm 0)
    (afterReduction : ∀ output, StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) whole output →
      Terminates built (evaluateC (encodeTm output) finishContinuation))
    {current : MClosed} (represented : SearchReadback.Rooted whole nextContinuation current) :
    Terminates built current := by
  obtain ⟨n, focus, stack, rfl, restored⟩ := represented
  refine .intro _ ?_
  intro after moved
  obtain ⟨output, reduced, pendingOrReturned⟩ := RootReadback.of_step built focus _ after moved
  have wholeStep : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows)
      whole (plug stack output) := by
    rw [← restored]
    exact (context stack).step (rules := DirectedSyntax.directedRules (Definitions.devPackage dev built.nativeRows)) reduced
  have evaluated := afterReduction (plug stack output) wholeStep
  have finalReturn := resume_eval built (plug stack output) evaluated
  have reconstruction := ContextProgress.reconstruct built (plug stack output) nextContinuation finalReturn
    (current := plugC (encodeTm output) (code stack) nextContinuation) ⟨n, output, stack, rfl, rfl⟩
  have rootReturn := resume_plug built output stack reconstruction
  rcases pendingOrReturned with pending | returned
  · exact HelperProgress.pending built output (plugContinuation stack) rootReturn pending
  · exact returned.symm ▸ rootReturn

theorem evaluate_normalizes {dev : Definitions.Development} (built : Compiled dev) (term : Tower.Tm 0)
    (source : Acc (fun after before =>
      StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after) term) :
    Terminates built (queryCode term) := by
  induction source with
  | intro term _ ih =>
      refine .intro _ ?_
      intro after moved
      rcases MainReadback.eval_step built (encodeTm term) finishContinuation after moved with value | search
      · subst after
        exact ValueWorkerRank.compiled_initialized_normalizes built (encodeTm term)
      · subst after
        exact ContextProgress.search built term nextContinuation
          (fun current represented => root built term ih represented)
          (SearchReadback.initial term nextContinuation)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.MachineProgress
