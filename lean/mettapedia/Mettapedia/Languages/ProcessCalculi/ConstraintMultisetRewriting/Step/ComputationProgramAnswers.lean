import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgramNoJunk
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgramComplete
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationCompleteness

/-!
# Source answers iff actual runs of the fixed descriptor program

The target side states only a restricted run and its actual final readout;
it does not request a source profile. Every target run obtains its profile
by the no-junk theorem. The one-live-row contract is explicit. Normality is
the package's normality; existence is not inferred from confluence.
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

def readout (state : State S.R Nat) (active : Nat) : Σ n : Nat, Tm Head n :=
  ⟨state.frame.arity, (state.label active).2.code⟩

omit [DecidableRel S.R.headEq] [DecidableEq Head] in
theorem execution_single {configuration : ComputationProfile.Configuration (S := S)}
    (execution : Execution qualified program.presentation configuration) :
    configuration.state.present = {configuration.active} →
      execution.last.state.present = {execution.last.active} := by
  induction execution with
  | nil => exact id
  | cons instruction target fresh rest ih =>
    intro single
    exact ih (next_single program qualified single instruction target fresh)

omit [DecidableEq Head] in
theorem restricted_readout {configuration : ComputationProfile.Configuration (S := S)}
    {run : (restricted program qualified).Run configuration.state}
    (profile : RunProfile qualified program.presentation configuration
      (Spaces.toRun (step S.levels Nat).toStep (permits program qualified) run))
    {active : Nat} (single : run.last.present = {active}) :
    readout run.last active = ⟨configuration.state.frame.arity, profile.execution.term⟩ := by
  have member : profile.execution.last.active ∈ run.last.present := by
    rw [← Spaces.toRun_last (step S.levels Nat).toStep (permits program qualified) run,
      profile.exact_endpoint]
    exact profile.execution.last.present
  have sameActive : profile.execution.last.active = active := by
    rw [single] at member
    exact Finset.mem_singleton.mp member
  have observation := full_run_readout qualified program.presentation profile
  change readout (Spaces.toRun (step S.levels Nat).toStep (permits program qualified) run).last
    profile.execution.last.active = _ at observation
  rw [Spaces.toRun_last, sameActive] at observation
  exact observation

theorem answers_by_program_iff (configuration : ComputationProfile.Configuration (S := S))
    (single : configuration.state.present = {configuration.active})
    (value : Tm Head configuration.state.frame.arity) :
    Answer S.R configuration.code value ↔
      ∃ run : (restricted program qualified).Run configuration.state,
        ∃ active : Nat, run.last.present = {active} ∧
          readout run.last active = ⟨configuration.state.frame.arity, value⟩ ∧
          ConstructorSystem.Normal S.R value := by
  constructor
  · rintro ⟨reductions, normal⟩
    obtain ⟨execution, endpoint⟩ := realize qualified program.presentation (configuration := configuration) reductions
    refine ⟨programRun program qualified execution, execution.last.active, ?_, ?_, normal⟩
    · rw [programRun_last]
      exact execution_single program qualified execution single
    · have observed : readout execution.last.state execution.last.active =
          ⟨configuration.state.frame.arity, execution.term⟩ := execution.final_readout
      rw [programRun_last]
      exact observed.trans (congrArg (Sigma.mk configuration.state.frame.arity) endpoint)
  · rintro ⟨run, active, finalSingle, observed, normal⟩
    obtain ⟨profile⟩ := configured_run_profiled program qualified configuration single run
    have sourceObserved := restricted_readout program qualified profile finalSingle
    have packed := sourceObserved.symm.trans observed
    have same : profile.execution.term = value := eq_of_heq (Sigma.mk.inj packed).2
    have reduces := profile.source_reduction
    rw [same] at reduces
    exact ⟨reduces, normal⟩

theorem normal_iff_no_program_firing (configuration : ComputationProfile.Configuration (S := S))
    (single : configuration.state.present = {configuration.active}) :
    ConstructorSystem.Normal S.R configuration.code ↔
      ¬ ∃ firing : Firing S.levels configuration.state, (restricted program qualified).Admits firing := by
  constructor
  · rintro normal ⟨firing, accepted⟩
    obtain ⟨proposal, _, present, _, reduction⟩ := every_admitted_firing_computes program qualified accepted
    have source : proposal.source = configuration.active := by
      rw [single] at present
      exact Finset.mem_singleton.mp present
    have reduction' : StepCore S.R.computation S.R.headEq configuration.code proposal.event.target := by
      have sameCode := congrArg (fun occurrence => (configuration.state.label occurrence).2.code) source
      have moved := Eq.mp (congrArg
        (fun term => StepCore S.R.computation S.R.headEq term proposal.event.target) sameCode) reduction
      exact moved
    exact normal reduction'
  · intro halted result reduction
    obtain ⟨instruction, _⟩ := source_complete (presentation := program.presentation) reduction
    exact halted ⟨instruction.compile qualified configuration.fresh,
      (instruction.admitted_iff qualified _).mpr configuration.fresh_absent,
      instruction_permitted program qualified instruction configuration.fresh⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.answers_by_program_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.normal_iff_no_program_firing
