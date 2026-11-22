import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationCompleteness

/-!
# Answer correspondence quantified over actual full-step runs

The target is the existing dependent full step. Its profile certificate
retains the selected redex and active occurrence throughout. The actual
endpoint is exactly the reified execution's complete state, not only an
equal final term. Normality is relative to the computational profile; the
general step continues to admit other resource operations.
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

theorem full_runs_iff {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity} :
    StepStar S.R configuration.code value ↔
      ∃ run : (step S.levels Nat).toStep.Run configuration.state,
        ∃ profile : RunProfile qualified presentation configuration run, profile.execution.term = value := by
  constructor
  · intro steps
    obtain ⟨execution, endpoint⟩ := realize qualified presentation steps
    refine ⟨execution.toRun, execution.profile, ?_⟩
    rw [execution.profile_execution]
    exact endpoint
  · rintro ⟨run, profile, rfl⟩
    exact profile.source_reduction

theorem full_answers_iff {configuration : Configuration (S := S)} {value : Tm Head configuration.state.frame.arity} :
    Answer S.R configuration.code value ↔
      ∃ run : (step S.levels Nat).toStep.Run configuration.state,
        ∃ profile : RunProfile qualified presentation configuration run,
          profile.execution.term = value ∧ ConstructorSystem.Normal S.R profile.execution.term := by
  constructor
  · rintro ⟨steps, normal⟩
    obtain ⟨run, profile, rfl⟩ := (full_runs_iff qualified presentation).mp steps
    exact ⟨run, profile, rfl, normal⟩
  · rintro ⟨run, profile, rfl, normal⟩
    exact ⟨profile.source_reduction, normal⟩

theorem full_conversion_answers_iff {configuration : Configuration (S := S)}
    {value : Tm Head configuration.state.frame.arity} :
    (Conv S.R.headEq configuration.code value S.R.computation ∧ ConstructorSystem.Normal S.R value) ↔
      ∃ run : (step S.levels Nat).toStep.Run configuration.state,
        ∃ profile : RunProfile qualified presentation configuration run,
          profile.execution.term = value ∧ ConstructorSystem.Normal S.R profile.execution.term :=
  (answer_iff qualified.churchRosser).symm.trans (full_answers_iff qualified presentation)

theorem normal_iff_no_instruction (configuration : Configuration (S := S)) :
    ConstructorSystem.Normal S.R configuration.code ↔ ¬ Nonempty (Instruction presentation configuration) := by
  constructor
  · intro normal ⟨instruction⟩
    exact normal instruction.reduction
  · intro none target reduction
    obtain ⟨instruction, _⟩ := source_complete (presentation := presentation) reduction
    exact none ⟨instruction⟩

theorem normal_iff_no_compiled_firing (configuration : Configuration (S := S)) :
    ConstructorSystem.Normal S.R configuration.code ↔
      ¬ ∃ instruction : Instruction presentation configuration,
        (step S.levels Nat).Admits (instruction.compile qualified configuration.fresh) := by
  rw [normal_iff_no_instruction presentation]
  constructor
  · rintro none ⟨instruction, _⟩
    exact none ⟨instruction⟩
  · rintro none ⟨instruction⟩
    exact none ⟨instruction, (instruction.admitted_iff qualified _).mpr configuration.fresh_absent⟩

theorem full_run_typed {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) :
    Typed S.R configuration.state.frame.raw profile.execution.term
      (configuration.state.label configuration.active).1.code := profile.execution.typed.1

theorem full_run_readout {configuration : Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : RunProfile qualified presentation configuration run) :
    (⟨run.last.frame.arity, (run.last.label profile.execution.last.active).2.code⟩ : Σ n : Nat, Tm Head n) =
      ⟨configuration.state.frame.arity, profile.execution.term⟩ := by
  have same := congrArg
    (fun state : State S.R Nat =>
      (⟨state.frame.arity, (state.label profile.execution.last.active).2.code⟩ : Σ n : Nat, Tm Head n))
    profile.exact_endpoint
  exact same.trans profile.execution.final_readout

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.full_conversion_answers_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.full_run_readout
