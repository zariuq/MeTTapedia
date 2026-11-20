import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgramAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationStreams

/-!
# Infinite runs of the descriptor program reflect source steps

The stream supplies actual restricted firings and their state updates, not
source instructions. Its one-live-row readout reflects one source step at
every index. Thus this backend erases no administrative steps. The source
relation here is explicitly the broad package relation, including head
equality; no fairness or termination of an arbitrary scheduler is claimed.
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

theorem firing_readout {state : State S.R Nat} {firing : Firing S.levels state}
    (accepted : (restricted program qualified).Admits firing)
    {before after : Nat} (singleBefore : state.present = {before})
    (singleAfter : ((restricted program qualified).result firing accepted).present = {after}) :
    ComputationProfile.Stream.ScopedStep (S := S) (readout state before)
      (readout ((restricted program qualified).result firing accepted) after) := by
  obtain ⟨proposal, same⟩ := accepted.2
  subst firing
  have shape := (proposal.admitted_iff qualified).mp accepted.1
  have source : proposal.source = before := by
    have member := shape.1
    rw [singleBefore] at member
    exact Finset.mem_singleton.mp member
  have target : proposal.target = after := by
    have member := ComputationResources.target_present S.levels state proposal.source proposal.target
      (proposal.output qualified) accepted.1
    change proposal.target ∈ ((restricted program qualified).result (proposal.compile qualified) accepted).present at member
    rw [singleAfter] at member
    exact Finset.mem_singleton.mp member
  refine ⟨state.frame.arity, (state.label before).2.code, proposal.event.target, rfl, ?_, ?_⟩
  · rw [← target]
    exact congrArg (fun row : TotalTerm state.frame =>
      (⟨state.frame.arity, row.2.code⟩ : Σ n : Nat, Tm Head n))
      (ComputationResources.result_label S.levels state proposal.source proposal.target
        (proposal.output qualified) accepted.1)
  · exact Eq.mp (congrArg
      (fun occurrence => StepCore S.R.computation S.R.headEq (state.label occurrence).2.code proposal.event.target)
      source) proposal.reduction

structure NativeStream where
  state : Nat → State S.R Nat
  active : Nat → Nat
  single : ∀ index, (state index).present = {active index}
  firing : ∀ index, Firing S.levels (state index)
  admitted : ∀ index, (restricted program qualified).Admits (firing index)
  advance : ∀ index, state (index + 1) = (restricted program qualified).result (firing index) (admitted index)

variable {program qualified}

def NativeStream.readout (stream : NativeStream program qualified) (index : Nat) : Σ n : Nat, Tm Head n :=
  ComputationProgram.readout (stream.state index) (stream.active index)

theorem NativeStream.source_step (stream : NativeStream program qualified) (index : Nat) :
    ComputationProfile.Stream.ScopedStep (S := S) (stream.readout index) (stream.readout (index + 1)) := by
  have singleAfter :
      ((restricted program qualified).result (stream.firing index) (stream.admitted index)).present =
        {stream.active (index + 1)} := by
    rw [← stream.advance index]
    exact stream.single (index + 1)
  have source := firing_readout program qualified (stream.admitted index) (stream.single index) singleAfter
  change ComputationProfile.Stream.ScopedStep (S := S)
    (ComputationProgram.readout (stream.state index) (stream.active index))
    (ComputationProgram.readout (stream.state (index + 1)) (stream.active (index + 1)))
  rw [stream.advance index]
  exact source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.NativeStream.source_step
