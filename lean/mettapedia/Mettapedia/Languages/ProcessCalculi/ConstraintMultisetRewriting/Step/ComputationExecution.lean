import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings

/-!
# Complete executions of the source-pinned computation profile

Each instruction compiles to one actual full-step firing. The execution
retains the scoped source instruction and the chosen fresh occurrence at
every stage, and exports the complete full-step run. There are no erased
administrative transitions in this realization.
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
  (qualified : Qualified S) {presentation : SchemaPresentation S.R}

def Instruction.next {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat)
    (fresh : target ∉ configuration.state.present) : Configuration (S := S) where
  state := (step S.levels Nat).toStep.result (instruction.compile qualified target)
    ((instruction.admitted_iff qualified target).mpr fresh)
  active := target
  present := ComputationResources.target_present S.levels configuration.state configuration.active target
    (instruction.output qualified) ((instruction.admitted_iff qualified target).mpr fresh)
  consistent := ComputationResources.result_consistent S.levels configuration.state configuration.active target
    (instruction.output qualified) ((instruction.admitted_iff qualified target).mpr fresh)

theorem Instruction.next_code {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat)
    (fresh : target ∉ configuration.state.present) :
    (instruction.next qualified target fresh).code = instruction.event.target :=
  congrArg (fun row : TotalTerm configuration.state.frame => row.2.code)
    (ComputationResources.result_label S.levels configuration.state configuration.active target
      (instruction.output qualified) ((instruction.admitted_iff qualified target).mpr fresh))

theorem Instruction.next_type {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration) (target : Nat)
    (fresh : target ∉ configuration.state.present) :
    ((instruction.next qualified target fresh).state.label target).1.code =
      (configuration.state.label configuration.active).1.code := by
  have same := ComputationResources.result_label S.levels configuration.state configuration.active target
    (instruction.output qualified) ((instruction.admitted_iff qualified target).mpr fresh)
  have types := congrArg (fun row : TotalTerm configuration.state.frame => row.1.code) same
  exact types

inductive Execution (presentation : SchemaPresentation S.R) : Configuration (S := S) → Type
  | nil (configuration : Configuration (S := S)) : Execution presentation configuration
  | cons {configuration : Configuration (S := S)} (instruction : Instruction presentation configuration)
      (target : Nat) (fresh : target ∉ configuration.state.present)
      (rest : Execution presentation (instruction.next qualified target fresh)) : Execution presentation configuration

namespace Execution

variable {qualified}

def last : {configuration : Configuration (S := S)} → Execution qualified presentation configuration → Configuration (S := S)
  | _, .nil configuration => configuration
  | _, .cons _ _ _ rest => rest.last

def term : {configuration : Configuration (S := S)} → Execution qualified presentation configuration →
    Tm Head configuration.state.frame.arity
  | _, .nil configuration => configuration.code
  | _, .cons _ _ _ rest => rest.term

def length : {configuration : Configuration (S := S)} → Execution qualified presentation configuration → Nat
  | _, .nil _ => 0
  | _, .cons _ _ _ rest => rest.length + 1

def toRun : {configuration : Configuration (S := S)} →
    Execution qualified presentation configuration → (step S.levels Nat).toStep.Run configuration.state
  | _, .nil configuration => .nil configuration.state
  | _, .cons instruction target fresh rest =>
      .cons (instruction.compile qualified target) ((instruction.admitted_iff qualified target).mpr fresh) rest.toRun

theorem toRun_last {configuration : Configuration (S := S)} (execution : Execution qualified presentation configuration) :
    execution.toRun.last = execution.last.state := by
  induction execution with
  | nil => rfl
  | cons _ _ _ _ ih => exact ih

theorem event_count {configuration : Configuration (S := S)} (execution : Execution qualified presentation configuration) :
    execution.toRun.word.length = execution.length := by
  induction execution with
  | nil => rfl
  | cons _ _ _ _ ih => exact congrArg (· + 1) ih

theorem final_readout {configuration : Configuration (S := S)} (execution : Execution qualified presentation configuration) :
    (⟨execution.last.state.frame.arity, execution.last.code⟩ : Σ n : Nat, Tm Head n) =
      ⟨configuration.state.frame.arity, execution.term⟩ := by
  induction execution with
  | nil => rfl
  | cons _ _ _ _ ih => exact ih

theorem reduces {configuration : Configuration (S := S)} (execution : Execution qualified presentation configuration) :
    StepStar S.R configuration.code execution.term := by
  induction execution with
  | nil => exact .refl
  | cons instruction target fresh rest ih =>
      rw [instruction.next_code qualified target fresh] at ih
      exact ih.head instruction.reduction

theorem typed {configuration : Configuration (S := S)} (execution : Execution qualified presentation configuration) :
    Typed S.R configuration.state.frame.raw execution.term
        (configuration.state.label configuration.active).1.code ∧
      Equal S.R configuration.state.frame.raw configuration.code execution.term
        (configuration.state.label configuration.active).1.code :=
  qualified.subjectReduction configuration.state.frame.formed execution.reduces
    (configuration.state.label configuration.active).2.typed

end Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.reduces
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.typed
