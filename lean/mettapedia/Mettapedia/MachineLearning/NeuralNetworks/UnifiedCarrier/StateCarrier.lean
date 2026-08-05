import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Recurrent
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipeline

/-!
# Unified fixed-address product carrier

This module packages the unified carrier's exact-real content, evidence, and
control planes as a nontrivial `StateCarrier`. Fixed addresses are represented
by an arbitrary slot type; allocation and legal-action support remain external
to the fast-state transition.

The endpoint theorem is relational rather than definitional. With Bayes
coupling and evidence/control readout disabled, the product carrier continues
to update its private evidence and control planes, while its complete finite
policy trajectory is equal to the existing scalar workspace endpoint under an
explicit simulation. Positive retained precision and recurrent-control
readout give separate strict-separation fixtures.

The routed precision scalars in `IndexedCommand` are an ideal-real interface.
Relating them to a concrete tensor evidence chart remains a source and
finite-precision conformance obligation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.MachineLearning.NeuralNetworks.Architecture
open Mettapedia.MachineLearning.NeuralNetworks.Architecture.StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.PLN.Evidence
open scoped ENNReal

universe uSlot

/-- Fixed-address product state: one content and evidence cell per slot, plus
one compact recurrent-control state. -/
abbrev IndexedState (Slot : Type uSlot) :=
  ProductState (Workspace Slot ℝ) (Slot → EvidenceLedger) ℝ

/-- One ideal-real command for the indexed product carrier. Precision values
are explicit routed inputs rather than silently inferred from a runtime tensor
chart. -/
structure IndexedCommand (Slot : Type uSlot) where
  contentProposal : Slot → ℝ
  learnedGate : Slot → ℝ
  routedOldPrecision : Slot → ℝ
  routedFreshPrecision : Slot → ℝ
  retention : Slot → ℝ≥0∞
  freshEvidence : Slot → WeightedEvidence
  controlInput : ℝ

/-- Route selected by one command. The content gain and evidence retention are
observable separately. -/
structure IndexedRoute (Slot : Type uSlot) where
  contentGain : Slot → ℝ
  retention : Slot → ℝ≥0∞

/-- Exact proposal for all three planes. -/
abbrev IndexedProposal (Slot : Type uSlot) := IndexedState Slot

/-- Slow parameters determine the evidence coupling and policy readout, while
the selected read slot exposes a finite-address observation. -/
structure IndexedMode (Slot : Type uSlot) where
  useBayesGain : Bool
  readSlot : Slot
  controlRetention : ℝ
  evidencePolicyWeight : ℝ
  controlPolicyWeight : ℝ

/-- Observation before the scalar policy readout. -/
structure IndexedObservation (Slot : Type uSlot) where
  content : Workspace Slot ℝ
  evidence : Slot → EvidenceLedger
  control : ℝ

/-- Signed posterior evidence used only as one explicit observation map. -/
noncomputable def signedPosterior (ledger : EvidenceLedger) : ℝ :=
  ledger.posterior.pos.toReal - ledger.posterior.neg.toReal

/-- Route a command through either the free learned gate or the
precision-damped gate. -/
noncomputable def indexedRoute
    {Slot : Type uSlot} (mode : IndexedMode Slot)
    (command : IndexedCommand Slot) : IndexedRoute Slot where
  contentGain := fun slot =>
    if mode.useBayesGain then
      command.learnedGate slot *
        precisionGain
          (command.routedOldPrecision slot)
          (command.routedFreshPrecision slot)
    else
      command.learnedGate slot
  retention := command.retention

/-- Propose every fixed-address content/evidence update and one recurrent
control update. -/
noncomputable def indexedProposal
    {Slot : Type uSlot} (mode : IndexedMode Slot)
    (command : IndexedCommand Slot) (state : IndexedState Slot)
    (route : IndexedRoute Slot) : IndexedProposal Slot where
  content := fun slot =>
    caromMix (state.content slot) (command.contentProposal slot)
      (route.contentGain slot)
  evidence := fun slot =>
    evidenceStep (route.retention slot) (state.evidence slot)
      (command.freshEvidence slot)
  control := command.controlInput + mode.controlRetention * state.control

/-- Common constructor. The mode map allows the full carrier and the exact
workspace endpoint to share one implementation. -/
noncomputable def indexedUnifiedCarrierWithMode
    {Slot : Type uSlot} {Slow : Type*}
    (modeAt : Slow → IndexedMode Slot) :
    StateCarrier (IndexedState Slot) Slow (IndexedCommand Slot)
      (IndexedState Slot) (IndexedState Slot) (IndexedRoute Slot)
      (IndexedProposal Slot) (IndexedObservation Slot) ℝ where
  initialState := fun initial _slow => initial
  read := fun _initial _slow state => state
  route := fun _initial slow command _state _read =>
    indexedRoute (modeAt slow) command
  propose := fun _initial slow command state _read route =>
    indexedProposal (modeAt slow) command state route
  write := fun _initial _slow _command _state _route proposal => proposal
  observe := fun _initial _slow state =>
    ⟨state.content, state.evidence, state.control⟩
  policy := fun _initial slow observation =>
    observation.content (modeAt slow).readSlot +
      (modeAt slow).evidencePolicyWeight *
        signedPosterior (observation.evidence (modeAt slow).readSlot) +
      (modeAt slow).controlPolicyWeight * observation.control

/-- Full indexed unified carrier. -/
noncomputable def indexedUnifiedCarrier
    {Slot : Type uSlot} :
    StateCarrier (IndexedState Slot) (IndexedMode Slot) (IndexedCommand Slot)
      (IndexedState Slot) (IndexedState Slot) (IndexedRoute Slot)
      (IndexedProposal Slot) (IndexedObservation Slot) ℝ :=
  indexedUnifiedCarrierWithMode id

/-- One structured step is exactly the routed three-plane proposal. -/
@[simp] theorem indexedUnifiedCarrier_step_eq
    {Slot : Type uSlot} (initial state : IndexedState Slot)
    (mode : IndexedMode Slot) (command : IndexedCommand Slot) :
    indexedUnifiedCarrier.step initial mode command state =
      indexedProposal mode command state (indexedRoute mode command) := rfl

/-- The content projection of one full carrier step is the existing scalar
content update at every fixed address. -/
theorem indexedUnifiedCarrier_step_content
    {Slot : Type uSlot} (initial state : IndexedState Slot)
    (mode : IndexedMode Slot) (command : IndexedCommand Slot)
    (slot : Slot) :
    (indexedUnifiedCarrier.step initial mode command state).content slot =
      contentStep mode.useBayesGain
        (state.content slot) (command.contentProposal slot)
        (command.learnedGate slot) (command.routedOldPrecision slot)
        (command.routedFreshPrecision slot) := by
  rfl

/-- The evidence projection is exactly fade-then-fuse plus innovation
accumulation through `evidenceStep`. -/
@[simp] theorem indexedUnifiedCarrier_step_evidence
    {Slot : Type uSlot} (initial state : IndexedState Slot)
    (mode : IndexedMode Slot) (command : IndexedCommand Slot)
    (slot : Slot) :
    (indexedUnifiedCarrier.step initial mode command state).evidence slot =
      evidenceStep (command.retention slot) (state.evidence slot)
        (command.freshEvidence slot) := rfl

/-- The compact recurrent-control projection has an explicit affine
recurrence. -/
@[simp] theorem indexedUnifiedCarrier_step_control
    {Slot : Type uSlot} (initial state : IndexedState Slot)
    (mode : IndexedMode Slot) (command : IndexedCommand Slot) :
    (indexedUnifiedCarrier.step initial mode command state).control =
      command.controlInput + mode.controlRetention * state.control := rfl

/-! ## Exact workspace endpoint as a policy simulation -/

/-- Slow endpoint parameters retain recurrent evolution privately but select
only workspace content for policy. -/
structure WorkspaceEndpointSlow (Slot : Type uSlot) where
  readSlot : Slot
  controlRetention : ℝ

/-- Endpoint mode: no Bayes content coupling and no evidence/control policy
residual. -/
def workspaceEndpointMode
    {Slot : Type uSlot} (slow : WorkspaceEndpointSlow Slot) :
    IndexedMode Slot where
  useBayesGain := false
  readSlot := slow.readSlot
  controlRetention := slow.controlRetention
  evidencePolicyWeight := 0
  controlPolicyWeight := 0

/-- Unified product carrier at its exact workspace endpoint. -/
noncomputable def indexedUnifiedWorkspaceEndpointCarrier
    {Slot : Type uSlot} :
    StateCarrier (IndexedState Slot) (WorkspaceEndpointSlow Slot)
      (IndexedCommand Slot) (IndexedState Slot) (IndexedState Slot)
      (IndexedRoute Slot) (IndexedProposal Slot) (IndexedObservation Slot) ℝ :=
  indexedUnifiedCarrierWithMode workspaceEndpointMode

/-- Reference scalar workspace carrier on the same fixed addresses and command
language. -/
noncomputable def indexedWorkspaceEndpointCarrier
    {Slot : Type uSlot} :
    StateCarrier (IndexedState Slot) (WorkspaceEndpointSlow Slot)
      (IndexedCommand Slot) (Workspace Slot ℝ) (Workspace Slot ℝ) Unit
      (Workspace Slot ℝ) (Workspace Slot ℝ) ℝ :=
  replacementCarrier
    (fun initial _slow => initial.content)
    (fun _initial _slow command state slot =>
      caromMix (state slot) (command.contentProposal slot)
        (command.learnedGate slot))
    (fun _initial _slow state => state)
    (fun _initial slow observation => observation slow.readSlot)

/-- Content equality is preserved even though the unified endpoint continues
to evolve private evidence and control state. -/
noncomputable def workspaceEndpointSimulation
    {Slot : Type uSlot} :
    StateCarrier.PolicySimulation
      (indexedWorkspaceEndpointCarrier (Slot := Slot))
      (indexedUnifiedWorkspaceEndpointCarrier (Slot := Slot)) where
  Rel := fun workspace unified => workspace = unified.content
  initialize_related := by
    intro initial slow
    rfl
  step_related := by
    intro initial slow command workspace unified related
    subst workspace
    rfl
  policy_related := by
    intro initial slow workspace unified related
    simpa [indexedWorkspaceEndpointCarrier,
      indexedUnifiedWorkspaceEndpointCarrier,
      indexedUnifiedCarrierWithMode, workspaceEndpointMode,
      replacementCarrier, StateCarrier.policyAtState,
      StateCarrier.observeAtState] using
      congrFun related slow.readSlot

/-- The complete finite policy trajectories agree at the workspace endpoint,
not merely one step. -/
theorem workspaceEndpoint_policyTrajectories_eq
    {Slot : Type uSlot} (initial : IndexedState Slot)
    (slow : WorkspaceEndpointSlow Slot)
    (commands : List (IndexedCommand Slot)) :
    (indexedWorkspaceEndpointCarrier (Slot := Slot)).policyTrajectoryFromInitial
        initial slow commands =
      (indexedUnifiedWorkspaceEndpointCarrier
        (Slot := Slot)).policyTrajectoryFromInitial initial slow commands :=
  workspaceEndpointSimulation.policyTrajectoryFromInitial_eq initial slow commands

/-! ## Strict separation and support fixtures -/

private noncomputable def zeroLedger : EvidenceLedger := ⟨0, 0⟩

private noncomputable def unitState (control : ℝ) : IndexedState Unit where
  content := fun _slot => 0
  evidence := fun _slot => zeroLedger
  control := control

private noncomputable def unitCommand : IndexedCommand Unit where
  contentProposal := fun _slot => 1
  learnedGate := fun _slot => 1
  routedOldPrecision := fun _slot => 1
  routedFreshPrecision := fun _slot => 1
  retention := fun _slot => 1
  freshEvidence := fun _slot => 0
  controlInput := 0

private def unitFullMode : IndexedMode Unit where
  useBayesGain := true
  readSlot := ()
  controlRetention := 1
  evidencePolicyWeight := 0
  controlPolicyWeight := 1

/-- Positive retained precision makes the full content update differ from the
workspace endpoint on a concrete fixed address. -/
theorem positivePrecision_fullCarrier_separates_workspace :
    (indexedUnifiedCarrier.step (unitState 0) unitFullMode unitCommand
      (unitState 0)).content () ≠
    (indexedWorkspaceEndpointCarrier.step (unitState 0)
      ⟨(), 1⟩ unitCommand (unitState 0).content) () := by
  norm_num [indexedUnifiedCarrier, indexedUnifiedCarrierWithMode,
    indexedProposal, indexedRoute, indexedWorkspaceEndpointCarrier,
    replacementCarrier, StateCarrier.step, precisionGain, caromMix,
    unitState, unitCommand, unitFullMode]

/-- Equal content and evidence snapshots with different recurrent histories
produce different full-carrier policies. -/
theorem recurrentHistory_fullPolicy_separates :
    indexedUnifiedCarrier.policyAtState (unitState 0) unitFullMode
        (unitState 0) ≠
      indexedUnifiedCarrier.policyAtState (unitState 0) unitFullMode
        (unitState 1) := by
  norm_num [indexedUnifiedCarrier, indexedUnifiedCarrierWithMode,
    StateCarrier.policyAtState, StateCarrier.observeAtState,
    signedPosterior, unitState, unitFullMode, zeroLedger]

/-- After any unified-carrier step, the common scorer's support remains
exactly the external legal mask. -/
theorem sourcePolicyAfterUnifiedStep_isSome
    {Slot : Type uSlot}
    {MemoryKey Operator MemoryValue Readout Embedding : Type*}
    [Fintype MemoryKey]
    [AddCommMonoid MemoryValue] [Module ℝ MemoryValue]
    (initial state : IndexedState Slot) (mode : IndexedMode Slot)
    (command : IndexedCommand Slot)
    (decision : IndexedState Slot → Decision)
    (memoryActive : MemoryKey → Bool)
    (memoryScore : Decision → MemoryKey → ℝ)
    (memoryValue : MemoryKey → MemoryValue)
    (readout : Decision → MemoryValue → Readout)
    (pairing : Readout → Embedding → ℝ)
    (operatorEmbedding : Operator → Embedding)
    (bias : Operator → ℝ) (legal : Operator → Bool)
    (operator : Operator) :
    (sourcePolicyReadout memoryActive memoryScore memoryValue readout pairing
      operatorEmbedding bias legal
      (decision (indexedUnifiedCarrier.step initial mode command state))
      operator).isSome = legal operator := by
  exact sourcePolicyReadout_isSome memoryActive memoryScore memoryValue readout
    pairing operatorEmbedding bias legal
    (decision (indexedUnifiedCarrier.step initial mode command state)) operator

/-- An adversarial full-carrier decision cannot make an illegal operator
appear in the common masked scorer. -/
theorem illegalOperator_stays_absent_after_unifiedStep :
    sourcePolicyReadout
      (fun _ : Unit => true)
      (fun decision : ℝ => fun _ : Unit => decision)
      (fun _ : Unit => (1 : ℝ))
      (fun decision context : ℝ => decision + context)
      (fun readout embedding : ℝ => readout * embedding)
      (fun operator : Bool => if operator then (2 : ℝ) else 1)
      (fun _ : Bool => (0 : ℝ))
      (fun operator : Bool => !operator)
      ((indexedUnifiedCarrier.step (unitState 0) unitFullMode unitCommand
        (unitState 0)).control)
      true = none := by
  simp [sourcePolicyReadout, legalMaskedScore]

#print axioms indexedUnifiedCarrier_step_content
#print axioms indexedUnifiedCarrier_step_evidence
#print axioms indexedUnifiedCarrier_step_control
#print axioms workspaceEndpoint_policyTrajectories_eq
#print axioms positivePrecision_fullCarrier_separates_workspace
#print axioms recurrentHistory_fullPolicy_separates
#print axioms sourcePolicyAfterUnifiedStep_isSome
#print axioms illegalOperator_stays_absent_after_unifiedStep

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
