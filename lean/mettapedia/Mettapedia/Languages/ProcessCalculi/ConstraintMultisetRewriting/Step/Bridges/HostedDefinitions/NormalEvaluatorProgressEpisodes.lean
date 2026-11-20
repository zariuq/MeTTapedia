import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RootReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorMachineView
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Administrative termination of one original-row evaluation episode

The actual context and helper readbacks compose with a terminating resume
boundary. The normal evaluator's next continuation will instantiate that
boundary. These original-row accessibility lemmas do not by themselves prove
termination of the enlarged source program or its recursive evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgressEpisodes

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextStack
open ContextProgress (Terminates)

variable {dev : Definitions.Development} (built : Compiled dev)

theorem resume_plug_normalizes {outer inner : Nat} (term : Tower.Tm inner)
    (stack : Stack outer inner) (continuation : MClosed)
    (following : Terminates built (plugC (encodeTm term) (code stack) continuation)) :
    Terminates built (resumeC (encodeTm term) (nodeC "hd-main-plug" [code stack, continuation])) := by
  refine .intro _ ?_
  intro next moved
  have same := MainReadback.resume_plug_step built (encodeTm term) (code stack) continuation next moved
  exact same.symm ▸ following

theorem root_normalizes {outer : Nat} (whole : Tower.Tm outer) (continuation : MClosed)
    (boundary : ∀ {n : Nat} (term : Tower.Tm n), Terminates built (resumeC (encodeTm term) continuation))
    {current : MClosed} (represented : SearchReadback.Rooted whole continuation current) :
    Terminates built current := by
  obtain ⟨n, focus, stack, rfl, _⟩ := represented
  refine .intro _ ?_
  intro next moved
  obtain ⟨output, _, pendingOrReturned⟩ := RootReadback.of_step built focus _ next moved
  have returned := boundary (plug stack output)
  have reconstruction := ContextProgress.reconstruct built (plug stack output) continuation returned
    (current := plugC (encodeTm output) (code stack) continuation) ⟨n, output, stack, rfl, rfl⟩
  have rootReturn := resume_plug_normalizes built output stack continuation reconstruction
  rcases pendingOrReturned with pending | finished
  · exact HelperProgress.pending built output (nodeC "hd-main-plug" [code stack, continuation]) rootReturn pending
  · exact finished.symm ▸ rootReturn

theorem search_normalizes {outer : Nat} (whole : Tower.Tm outer) (continuation : MClosed)
    (boundary : ∀ {n : Nat} (term : Tower.Tm n), Terminates built (resumeC (encodeTm term) continuation))
    {current : MClosed} (represented : SearchReadback.Seeking whole continuation current) :
    Terminates built current :=
  ContextProgress.search built whole continuation
    (fun _ rooted => root_normalizes built whole continuation boundary rooted) represented

theorem resume_normalizes {n : Nat} (term : Tower.Tm n) :
    Terminates built (resumeC (encodeTm term) NormalEvaluatorMachineView.nextContinuation) := by
  refine .intro _ ?_
  intro next moved
  exact False.elim (NormalEvaluatorMachineView.no_original_return_step built _ _ moved)

theorem episode_normalizes {before : Tower.Tm 0} {current : MClosed}
    (known : NormalEvaluatorMachineView.Episode built before current) : Terminates built current := by
  cases known with
  | searching search =>
      exact search_normalizes built before NormalEvaluatorMachineView.nextContinuation
        (fun term => resume_normalizes built term) search
  | rooted root =>
      exact root_normalizes built before NormalEvaluatorMachineView.nextContinuation
        (fun term => resume_normalizes built term) root
  | pending result stack _ helper =>
      have reconstruction := ContextProgress.reconstruct built (plug stack result)
        NormalEvaluatorMachineView.nextContinuation (resume_normalizes built (plug stack result))
        (current := plugC (encodeTm result) (code stack) NormalEvaluatorMachineView.nextContinuation)
        ⟨_, result, stack, rfl, rfl⟩
      have returned := resume_plug_normalizes built result stack NormalEvaluatorMachineView.nextContinuation reconstruction
      exact HelperProgress.pending built result (NormalEvaluatorMachineView.plugContinuation stack) returned helper
  | resumingPlug result stack _ =>
      have reconstruction := ContextProgress.reconstruct built (plug stack result)
        NormalEvaluatorMachineView.nextContinuation (resume_normalizes built (plug stack result))
        (current := plugC (encodeTm result) (code stack) NormalEvaluatorMachineView.nextContinuation)
        ⟨_, result, stack, rfl, rfl⟩
      exact resume_plug_normalizes built result stack NormalEvaluatorMachineView.nextContinuation reconstruction
  | plugging after _ reconstruct =>
      exact ContextProgress.reconstruct built after NormalEvaluatorMachineView.nextContinuation
        (resume_normalizes built after) reconstruct
  | resuming after _ => exact resume_normalizes built after

theorem episode_rank_lt {before : Tower.Tm 0} {current after : MClosed}
    (known : NormalEvaluatorMachineView.Episode built before current)
    (moved : ProgramBinders.Rewrites built.rules.get current after) :
    (episode_normalizes built (NormalEvaluatorMachineView.step built known moved)).rank <
      (episode_normalizes built known).rank :=
  Acc.rank_lt_of_rel (episode_normalizes built known) moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgressEpisodes

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgressEpisodes.episode_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgressEpisodes.episode_rank_lt
