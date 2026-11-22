import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationContinuation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSyntaxConsumer

/-!
# A dependent consumer actually publishes after the interpreter runs

The first segment consists of the qualified interpreter's computation firings.
The second segment is a separately admitted typed publication. It consumes
the computed value and publishes a proof whose annotation still mentions the
original call. The complete state, source publication and occurrence update
are retained; the extra action is not called a reduction of the value.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {run : (step setting.levels Nat).toStep.Run start.state}
  (profile : RunProfile qualified presentation start run)

def consumerRun : (step setting.levels Nat).toStep.Run run.last :=
  Continuation.fullRun profile.finalConfiguration (proofRow run.last.frame)
    profile.finalConfiguration.fresh profile.finalConfiguration.fresh_absent

def followed : (step setting.levels Nat).toStep.Run start.state := run.append (consumerRun profile)

def readout (state : State package Nat) (active : Nat) : Σ n : Nat, Tower.Tm n × Tower.Tm n :=
  ⟨state.frame.arity, (state.label active).1.code, (state.label active).2.code⟩

theorem followed_readout :
    readout (followed profile).last profile.finalConfiguration.fresh =
      ⟨run.last.frame.arity, claim, .refl (number 5)⟩ := by
  have endState := Step.Run.last_append run (consumerRun profile)
  have endRead := congrArg (fun state => readout state profile.finalConfiguration.fresh) endState
  apply endRead.trans
  unfold readout
  have label := Continuation.fullRun_output profile.finalConfiguration (proofRow run.last.frame)
    profile.finalConfiguration.fresh profile.finalConfiguration.fresh_absent
  exact congrArg (fun row : TotalTerm run.last.frame =>
    (⟨run.last.frame.arity, row.1.code, row.2.code⟩ : Σ n : Nat, Tower.Tm n × Tower.Tm n)) label

theorem followed_target_present :
    profile.finalConfiguration.fresh ∈ (followed profile).last.present := by
  change profile.finalConfiguration.fresh ∈ (run.append (consumerRun profile)).last.present
  rw [Step.Run.last_append]
  exact Continuation.fullRun_target profile.finalConfiguration (proofRow run.last.frame)
    profile.finalConfiguration.fresh profile.finalConfiguration.fresh_absent

theorem followed_event_count : (followed profile).word.length = run.word.length + 1 := by
  unfold followed
  rw [Step.Run.word_append, List.length_append]
  rfl

theorem actual_dependent_consumer :
    ∃ run : (step setting.levels Nat).toStep.Run start.state,
      ∃ profile : RunProfile qualified presentation start run,
        profile.execution.term = number 5 ∧
          readout (followed profile).last profile.finalConfiguration.fresh =
            ⟨run.last.frame.arity, claim, .refl (number 5)⟩ ∧
          profile.finalConfiguration.fresh ∈ (followed profile).last.present ∧
          (followed profile).word.length = run.word.length + 1 := by
  obtain ⟨run, profile, answer, _⟩ := interpreter_has_full_run
  exact ⟨run, profile, answer, followed_readout profile,
    followed_target_present profile, followed_event_count profile⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.SyntaxConsumer.actual_dependent_consumer
