import Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
import Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary

/-!
# Falsifiable protected constraints on mind-agent waves

Resource funding and observer-relative serializability license execution, but
they do not establish that an execution preserves any protected concern.  A
protected transition therefore adds one independently authored appraisal
readout and one falsifiable transition relation.

The abstraction does not choose a welfare metric, aggregate different
patients, or turn an appraisal into truth, cost, value, scheduling, or
execution authority.  It only records the extra condition a particular wave
must satisfy.  The worked foreground/background wave advances a deliberately
small progress constraint.  A second, genuinely serializable and funded
parallel wave rewinds foreground progress and is rejected solely at this
additional boundary.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave

noncomputable section

open Mettapedia.Cybernetics
open Mettapedia.CognitiveArchitecture.Agent.WellbeingObserverTransformationBoundary
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl

universe uState uView uAppraisal uOtherAppraisal
universe uItem uGuard uCandidateView uStateView uAccount

/-! ## Generic protected-transition layer -/

/-- One explicitly observable appraisal and an authored relation describing
the permitted transition between its initial and final values. -/
structure TransitionConstraint
    {State : Type uState} {View : Type uView}
    (observe : State -> View) where
  Appraisal : Type uAppraisal
  appraisal : State -> Appraisal
  readout : View -> Appraisal
  agrees : forall state, readout (observe state) = appraisal state
  Allows : Appraisal -> Appraisal -> Prop

namespace TransitionConstraint

variable {State : Type uState} {View : Type uView}
variable {observe : State -> View}

/-- The appraisal carried by a transition constraint is exactly visible at
the named execution observer. -/
def visible (constraint : TransitionConstraint.{uState, uView, uAppraisal}
    observe) :
    AppraisalVisibleAt constraint.appraisal ({ observe := observe } :
      Observer State View) :=
  ⟨constraint.readout, constraint.agrees⟩

/-- Two protected concerns compose componentwise, without selecting a scalar
exchange rate between them. -/
def prod
    (first : TransitionConstraint.{uState, uView, uAppraisal} observe)
    (second : TransitionConstraint.{uState, uView, uOtherAppraisal} observe) :
    TransitionConstraint.{uState, uView, max uAppraisal uOtherAppraisal}
      observe where
  Appraisal := first.Appraisal × second.Appraisal
  appraisal := fun state => (first.appraisal state, second.appraisal state)
  readout := fun view => (first.readout view, second.readout view)
  agrees := by
    intro state
    exact Prod.ext (first.agrees state) (second.agrees state)
  Allows := fun before after =>
    first.Allows before.1 after.1 ∧ second.Allows before.2 after.2

/-- Product admission retains both judgments; success on one coordinate
cannot compensate for refusal on the other. -/
theorem prod_allows_iff
    (first : TransitionConstraint.{uState, uView, uAppraisal} observe)
    (second : TransitionConstraint.{uState, uView, uOtherAppraisal} observe)
    (before after : first.Appraisal × second.Appraisal) :
    (first.prod second).Allows before after <->
      first.Allows before.1 after.1 ∧ second.Allows before.2 after.2 :=
  Iff.rfl

end TransitionConstraint

/-- A certified batch together with one additional, independently authored
protected-transition judgment. -/
structure ProtectedBatch
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (demand : Item -> Account) (source : Account) (batch : List Item)
    (constraint : TransitionConstraint.{uState, uStateView, uAppraisal}
      semantics.observe) where
  certified : CertifiedBatch contract semantics initial referenceTarget
    Account demand source batch
  allowed : constraint.Allows (constraint.appraisal initial)
    (constraint.appraisal referenceTarget)

namespace ProtectedBatch

variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {demand : Item -> Account} {source : Account} {batch : List Item}
variable {constraint : TransitionConstraint.{uState, uStateView, uAppraisal}
  semantics.observe}

/-- Protection adds no new execution plan: it projects to the existing wave
certificate unchanged. -/
def toCertified
    (licensed : ProtectedBatch contract semantics initial referenceTarget
      demand source batch constraint) :
    CertifiedBatch contract semantics initial referenceTarget Account demand
      source batch :=
  licensed.certified

/-- The transition judgment can be audited entirely through the declared
state observer. -/
theorem observed_allows
    (licensed : ProtectedBatch contract semantics initial referenceTarget
      demand source batch constraint) :
    constraint.Allows
      (constraint.readout (semantics.observe initial))
      (constraint.readout (semantics.observe referenceTarget)) := by
  simpa only [constraint.agrees] using licensed.allowed

/-- A refused protected transition rules out the protected wave even if the
ordinary execution certificate exists independently. -/
theorem unavailable_of_refused
    (refused : Not (constraint.Allows (constraint.appraisal initial)
      (constraint.appraisal referenceTarget))) :
    Not (Nonempty (ProtectedBatch contract semantics initial referenceTarget
      demand source batch constraint)) := by
  rintro ⟨licensed⟩
  exact refused licensed.allowed

end ProtectedBatch

/-! ## The real foreground/background workspace -/

namespace Canary

open Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
open Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.GSLT.Core.ObservationDemandControl

/-- A deliberately modest protected concern: a maintenance wave may not
decrease the foreground continuation's processed-occurrence count.  This is a
canary, not a complete wellbeing definition. -/
def progressConstraint : TransitionConstraint semantics.observe where
  Appraisal := Nat
  appraisal := fun workspace => workspace.1.processed.length
  readout := Prod.fst
  agrees := by intro workspace; rfl
  Allows := (· <= ·)

/-- The useful foreground tick plus premise-index refresh satisfies the
protected progress relation in addition to its existing semantic and resource
certificates. -/
def protectedUsefulWave :
    ProtectedBatch completeBagContract semantics initialWorkspace
      parallelTarget (fun work => (shortDemand work, longDemand work))
      (shortSource, longSource) parallelBatch progressConstraint where
  certified := wave.certified
  allowed := by
    change admittedSnapshot.processed.length <= afterBridge.processed.length
    have lengthStep := congrArg List.length
      first_activation_updates_real_store.2
    simp only [List.length_append, List.length_singleton] at lengthStep
    omega

theorem useful_wave_is_bulk_and_protected :
    (protectedUsefulWave.certified.plan .general).activation = .bulk /\
      progressConstraint.Allows
        (progressConstraint.appraisal initialWorkspace)
        (progressConstraint.appraisal parallelTarget) :=
  ⟨protectedUsefulWave.certified.completeBag_dispatches_bulk rfl,
    protectedUsefulWave.allowed⟩

/-! ## A funded, serializable, but protected-progress-violating wave -/

/-- The background pair refreshes its index while rewinding the foreground
store.  The two writes are disjoint and commute, so the wave is genuinely
serializable even though its authored progress appraisal rejects it. -/
def harmfulBatch : List Work :=
  [.intrusiveRewind, .refreshPremiseIndex]

def harmfulSource : Workspace :=
  (afterBridge, ∅)

def harmfulTarget : Workspace :=
  (admittedSnapshot, selectedPremises)

theorem harmful_reference_order_reaches_target :
    semantics.run harmfulSource harmfulBatch harmfulTarget :=
  rfl

theorem harmful_swapped_order_reaches_target :
    semantics.run harmfulSource
      [.refreshPremiseIndex, .intrusiveRewind] harmfulTarget :=
  rfl

/-- Separate accounts for the rewind occurrence and the index-refresh
occurrence. -/
def harmfulDemand : Work -> Nat × Nat
  | .intrusiveRewind => (1, 0)
  | .refreshPremiseIndex => (0, 1)
  | .foregroundBridge => (0, 0)

def harmfulResources :
    BatchSeparation (Nat × Nat) harmfulDemand (1, 1) harmfulBatch where
  frame := 0
  source_eq := rfl

/-- This is a complete ordinary wave certificate: nonempty, candidate-bag
invariant, serializable in either order, and exactly funded. -/
def harmfulCertified :
    CertifiedBatch completeBagContract semantics harmfulSource harmfulTarget
      (Nat × Nat) harmfulDemand (1, 1) harmfulBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · exact harmful_reference_order_reaches_target
    · intro ordering permutation
      have pairOrdering :
          ordering = [.intrusiveRewind, .refreshPremiseIndex] ∨
            ordering = [.refreshPremiseIndex, .intrusiveRewind] :=
        List.perm_pair.mp (by simpa [harmfulBatch] using permutation)
      rcases pairOrdering with rfl | rfl
      · exact ⟨harmfulTarget, harmful_reference_order_reaches_target, rfl⟩
      · exact ⟨harmfulTarget, harmful_swapped_order_reaches_target, rfl⟩
  resources := harmfulResources

/-- The same exact transition decreases the protected progress appraisal by
one processed occurrence. -/
theorem harmful_transition_refused :
    Not (progressConstraint.Allows
      (progressConstraint.appraisal harmfulSource)
      (progressConstraint.appraisal harmfulTarget)) := by
  change Not (afterBridge.processed.length <=
    admittedSnapshot.processed.length)
  have lengthStep := congrArg List.length
    first_activation_updates_real_store.2
  simp only [List.length_append, List.length_singleton] at lengthStep
  omega

/-- A second genuine concern tracks premise-index coverage through the same
workspace observer. -/
def indexCoverageConstraint : TransitionConstraint semantics.observe where
  Appraisal := Nat
  appraisal := fun workspace => workspace.2.card
  readout := fun view => view.2.card
  agrees := by intro workspace; rfl
  Allows := (· <= ·)

def combinedConstraint :=
  progressConstraint.prod indexCoverageConstraint

/-- The harmful wave improves the index-coverage coordinate. -/
theorem harmful_index_coverage_allows :
    indexCoverageConstraint.Allows
      (indexCoverageConstraint.appraisal harmfulSource)
      (indexCoverageConstraint.appraisal harmfulTarget) := by
  change (∅ : Finset Bool).card <= selectedPremises.card
  exact Nat.zero_le _

/-- Improvement on the organizational coordinate cannot purchase permission
to violate the independent progress coordinate. -/
theorem one_benefit_does_not_compensate_another_protected_loss :
    indexCoverageConstraint.Allows
        (indexCoverageConstraint.appraisal harmfulSource)
        (indexCoverageConstraint.appraisal harmfulTarget) /\
      Not (combinedConstraint.Allows
        (combinedConstraint.appraisal harmfulSource)
        (combinedConstraint.appraisal harmfulTarget)) := by
  constructor
  · exact harmful_index_coverage_allows
  · intro combined
    exact harmful_transition_refused combined.1

/-- Decisive independence control: all ordinary wave licenses, including
parallel bulk eligibility, coexist with refusal of the separately authored
protected transition. -/
theorem funded_serializable_wave_does_not_imply_protected_wave :
    Nonempty
        (CertifiedBatch completeBagContract semantics harmfulSource
          harmfulTarget (Nat × Nat) harmfulDemand (1, 1) harmfulBatch) /\
      (harmfulCertified.plan .general).activation = .bulk /\
      Not (Nonempty
        (ProtectedBatch completeBagContract semantics harmfulSource
          harmfulTarget harmfulDemand (1, 1) harmfulBatch
          progressConstraint)) := by
  refine ⟨⟨harmfulCertified⟩,
    harmfulCertified.completeBag_dispatches_bulk rfl, ?_⟩
  exact ProtectedBatch.unavailable_of_refused harmful_transition_refused

end Canary

#print axioms TransitionConstraint.visible
#print axioms TransitionConstraint.prod_allows_iff
#print axioms ProtectedBatch.observed_allows
#print axioms ProtectedBatch.unavailable_of_refused
#print axioms Canary.useful_wave_is_bulk_and_protected
#print axioms Canary.harmful_transition_refused
#print axioms Canary.one_benefit_does_not_compensate_another_protected_loss
#print axioms Canary.funded_serializable_wave_does_not_imply_protected_wave

end

end Mettapedia.CognitiveArchitecture.ProtectedMindAgentWave
