import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationExecution

/-!
# Source-origin certificates indexed by existing full-step runs

This grammar licenses exactly the compiled computational firing at each
stage of an actual run. Its data are source instructions and occurrence
choices, not assumptions of source reachability. Reification retains the
literal full-step run, including its knowledge and resource effects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (qualified : Qualified S) (presentation : SchemaPresentation S.R)

inductive RunProfile : (configuration : Configuration (S := S)) →
    (step S.levels Nat).toStep.Run configuration.state → Type
  | nil (configuration : Configuration (S := S)) : RunProfile configuration (.nil configuration.state)
  | cons {configuration : Configuration (S := S)} (instruction : Instruction presentation configuration)
      (target : Nat) (fresh : target ∉ configuration.state.present)
      {rest : (step S.levels Nat).toStep.Run (instruction.next qualified target fresh).state}
      (later : RunProfile (instruction.next qualified target fresh) rest) :
      RunProfile configuration
        (.cons (instruction.compile qualified target) ((instruction.admitted_iff qualified target).mpr fresh) rest)

namespace RunProfile

variable {qualified presentation}

def execution : {configuration : Configuration (S := S)} →
    {run : (step S.levels Nat).toStep.Run configuration.state} →
    RunProfile qualified presentation configuration run → Execution qualified presentation configuration
  | _, _, .nil configuration => .nil configuration
  | _, _, .cons instruction target fresh later => .cons instruction target fresh later.execution

theorem exact_run {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) : profile.execution.toRun = run := by
  induction profile with
  | nil => rfl
  | cons instruction target fresh later ih => exact congrArg (Step.Run.cons _ _) ih

theorem exact_endpoint {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) :
    run.last = profile.execution.last.state :=
  (congrArg Step.Run.last profile.exact_run).symm.trans profile.execution.toRun_last

theorem source_reduction {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) :
    StepStar S.R configuration.code profile.execution.term := profile.execution.reduces

theorem event_count {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) :
    run.word.length = profile.execution.length := by
  exact (congrArg (fun path => path.word.length) profile.exact_run).symm.trans profile.execution.event_count

end RunProfile

namespace Execution

variable {qualified presentation}

def profile : {configuration : Configuration (S := S)} →
    (execution : Execution qualified presentation configuration) →
    RunProfile qualified presentation configuration execution.toRun
  | _, .nil configuration => .nil configuration
  | _, .cons instruction target fresh rest => .cons instruction target fresh rest.profile

theorem profile_execution {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration) : execution.profile.execution = execution := by
  induction execution with
  | nil => rfl
  | cons instruction target fresh rest ih => exact congrArg (Execution.cons instruction target fresh) ih

end Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.RunProfile.exact_run
