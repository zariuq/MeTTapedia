import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunProfile

/-!
# Every source computation is a run of the fixed descriptor program

The existing structural decoder supplies a valid finite code for each source
instruction. Its original table ordinal remains available in the proposal.
The permitted run is a restriction of the actual full-step run, with exactly
the same firings, endpoint and event count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing ComputationProfile

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (program : Program S.R) [DecidableRel S.R.headEq] [DecidableEq Head] (qualified : Qualified S)

def fromSubmission {configuration : ComputationProfile.Configuration (S := S)}
    (submission : ComputationReplay.Submission program.presentation program.table program.same configuration)
    (target : Nat) : Proposal program configuration.state :=
  ⟨configuration.active, target, submission.code, submission.event, submission.parsed, submission.source⟩

theorem instruction_permitted {configuration : ComputationProfile.Configuration (S := S)}
    (instruction : Instruction program.presentation configuration) (target : Nat) :
    permits program qualified (instruction.compile qualified target) := by
  obtain ⟨_, submission, _, endpoint⟩ :=
    ComputationReplay.source_has_submission program.presentation program.table program.same instruction.reduction
  refine ⟨fromSubmission program submission target, ?_⟩
  have output : submission.instruction.output qualified = instruction.output qualified :=
    totalTerm_ext rfl endpoint
  change ComputationResources.firing S.levels configuration.state configuration.active target
      (submission.instruction.output qualified) =
    ComputationResources.firing S.levels configuration.state configuration.active target (instruction.output qualified)
  exact congrArg (ComputationResources.firing S.levels configuration.state configuration.active target) output

def programRun {configuration : ComputationProfile.Configuration (S := S)} :
    Execution qualified program.presentation configuration → (restricted program qualified).Run configuration.state
  | .nil configuration => .nil configuration.state
  | .cons instruction target fresh rest =>
    .cons (instruction.compile qualified target)
      ⟨(instruction.admitted_iff qualified target).mpr fresh,
        instruction_permitted program qualified instruction target⟩ (programRun rest)

theorem programRun_forget {configuration : ComputationProfile.Configuration (S := S)}
    (execution : Execution qualified program.presentation configuration) :
    Spaces.toRun (step S.levels Nat).toStep (permits program qualified) (programRun program qualified execution) =
      execution.toRun := by
  induction execution with
  | nil => rfl
  | cons instruction target fresh rest ih =>
    simpa only [programRun, Spaces.toRun, Execution.toRun] using
      congrArg (Step.Run.cons (instruction.compile qualified target)
        ((instruction.admitted_iff qualified target).mpr fresh)) ih

theorem programRun_last {configuration : ComputationProfile.Configuration (S := S)}
    (execution : Execution qualified program.presentation configuration) :
    (programRun program qualified execution).last = execution.last.state := by
  have same := congrArg (fun run : (step S.levels Nat).toStep.Run configuration.state => run.last)
    (programRun_forget program qualified execution)
  exact (Spaces.toRun_last _ _ _).symm.trans (same.trans execution.toRun_last)

theorem programRun_events {configuration : ComputationProfile.Configuration (S := S)}
    (execution : Execution qualified program.presentation configuration) :
    (programRun program qualified execution).word.length = execution.length := by
  have same := congrArg (fun run : (step S.levels Nat).toStep.Run configuration.state => run.word.length)
    (programRun_forget program qualified execution)
  exact (congrArg List.length (Spaces.toRun_word _ _ _)).symm.trans (same.trans execution.event_count)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.instruction_permitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.programRun_forget
