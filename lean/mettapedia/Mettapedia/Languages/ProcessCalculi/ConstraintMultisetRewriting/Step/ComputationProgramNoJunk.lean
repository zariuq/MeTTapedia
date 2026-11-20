import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers

/-!
# Every run of the fixed descriptor program has a source computation

With one live computational row, native admission determines which row the
program consumes. Every restricted firing therefore reconstructs an
instruction, and every restricted run reconstructs a source profile. The
client supplies no profile. The exact unrestricted full-step run is retained.
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
  (program : Program S.R) [DecidableRel S.R.headEq] (qualified : Qualified S)

def singleConfiguration (state : State S.R Nat) (active : Nat) (single : state.present = {active})
    (consistent : (frames S.levels).Solvable state.knowledge) : ComputationProfile.Configuration (S := S) :=
  ⟨state, active, by rw [single]; exact Finset.mem_singleton_self _, consistent⟩

omit [DecidableRel S.R.headEq] in
theorem next_single {configuration : ComputationProfile.Configuration (S := S)}
    (single : configuration.state.present = {configuration.active})
    (instruction : Instruction program.presentation configuration) (target : Nat)
    (fresh : target ∉ configuration.state.present) :
    (instruction.next qualified target fresh).state.present = {target} := by
  change (configuration.state.present \ {configuration.active}) ∪ {target} = {target}
  rw [single]
  simp

theorem every_run_profiled {state : State S.R Nat}
    (run : (restricted program qualified).Run state) :
    ∀ (active : Nat) (single : state.present = {active})
      (consistent : (frames S.levels).Solvable state.knowledge),
      Nonempty (RunProfile qualified program.presentation (singleConfiguration state active single consistent)
        (Spaces.toRun (step S.levels Nat).toStep (permits program qualified) run)) := by
  induction run with
  | nil state =>
    intro active single consistent
    exact ⟨.nil (singleConfiguration state active single consistent)⟩
  | @cons state firing accepted rest ih =>
    intro active single consistent
    obtain ⟨proposal, same⟩ := accepted.2
    subst firing
    have shape := (proposal.admitted_iff qualified).mp accepted.1
    have source : proposal.source = active := by
      have present := shape.1
      rw [single] at present
      exact Finset.mem_singleton.mp present
    rcases proposal with ⟨sourceIndex, target, code, event, parsed, aligned⟩
    change sourceIndex = active at source
    subst sourceIndex
    let configuration := singleConfiguration state active single consistent
    let instruction : Instruction program.presentation configuration := ⟨event, aligned⟩
    have fresh : target ∉ state.present := shape.2.1
    have nextSingle := next_single program qualified single instruction target fresh
    have nextConsistent := (instruction.next qualified target fresh).consistent
    obtain ⟨later⟩ := ih target nextSingle nextConsistent
    change RunProfile qualified program.presentation (instruction.next qualified target fresh)
      (Spaces.toRun (step S.levels Nat).toStep (permits program qualified) rest) at later
    exact ⟨.cons instruction target fresh later⟩

theorem configured_run_profiled (configuration : ComputationProfile.Configuration (S := S))
    (single : configuration.state.present = {configuration.active})
    (run : (restricted program qualified).Run configuration.state) :
    Nonempty (RunProfile qualified program.presentation configuration
      (Spaces.toRun (step S.levels Nat).toStep (permits program qualified) run)) := by
  have profile := every_run_profiled program qualified run configuration.active single configuration.consistent
  exact profile

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.every_run_profiled
