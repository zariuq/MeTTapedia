import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDispatch
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrainPreservation

/-!
# Source-bound physical assertion launch through normal dispatch

An authored compressed-proof byte selects an assertion in the source heap.
The compiler-produced assertion launcher then fires in the actual rule-scoped
MORK scheduler, four obsolete predecessor probes drain inertly, and the
captured normal-dispatch bridge fires.  The six concrete transitions form one
nonempty proof-relevant trace, and OSLF classifies that same trace.

The endpoint here is the literal physical result of firing the normal-dispatch
bridge.  Exact reload publication and the subsequent normal-verifier execution
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionLaunchToDispatch

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDispatch
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrain
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeDrainPreservation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeExactMembership
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The source-derived physical state before the assertion launcher fires. -/
def physicalSourceAssertionInitial
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  sourceDecoratedAssertionBridgeReadySpace context state ledger scanner index
    cursor assertion

/-- The physical state immediately after the assertion launcher fires. -/
def physicalSourceAssertionLaunched
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  sourceAssertionBridgeLaunchResult
    (physicalSourceAssertionInitial context state ledger scanner index cursor
      assertion)

/-- The physical state after all four obsolete predecessor probes drain. -/
def physicalSourceAssertionDrained
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  afterLookupAdvanceProbe
    (physicalSourceAssertionLaunched context state ledger scanner index cursor
      assertion)

/-- The literal physical result of firing the captured normal-dispatch bridge. -/
def physicalSourceAssertionDispatched
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  cFireRuleScopedSourceExecFact
    (physicalSourceAssertionDrained context state ledger scanner index cursor
      assertion)
    compressedNormalDispatchBridgeDirective

/-- One source-authorized compressed assertion request advances through the
launcher, four predecessor drains, and normal dispatch in six actual physical
MORK transitions.  The witness stores the execution trace, not an asserted
successor state. -/
structure PhysicalSourceAssertionLaunchToDispatchSegment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Type where
  request : SourceAssertionRequest context state scannerBefore scannerAfter
    occurrence index assertion
  sourceScannerStep :
    SourceStep (.request occurrence scannerBefore.phase)
      (.outcome occurrence (.decoded [.step index] scannerAfter.phase))
  assertionAuthored : assertion ∈ source.assertions
  heapRowSourceDerived :
    sourceAssertionHeapRow (source := source) context.proofOwner index assertion ∈
      assertionHeapRows context.proofOwner state.heap
  initialListNodup :
    (physicalSourceAssertionInitial context state ledger scannerAfter index
      cursor assertion).Nodup
  initialMorkNodup : MorkSupportNodup
    (physicalSourceAssertionInitial context state ledger scannerAfter index
      cursor assertion)
  launchStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (physicalSourceAssertionInitial context state ledger scannerAfter index
        cursor assertion) =
    some (physicalSourceAssertionLaunched context state ledger scannerAfter
      index cursor assertion)
  predecessorDrain : PhysicalAssertionPredecessorDrain
    (physicalSourceAssertionLaunched context state ledger scannerAfter index
      cursor assertion)
    (physicalSourceAssertionDrained context state ledger scannerAfter index
      cursor assertion)
  bridgeMember : compressedNormalDispatchBridgeRule ∈
    physicalSourceAssertionDrained context state ledger scannerAfter index
      cursor assertion
  dispatchStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (physicalSourceAssertionDrained context state ledger scannerAfter index
        cursor assertion) =
    some (physicalSourceAssertionDispatched context state ledger scannerAfter
      index cursor assertion)
  trace : CRuleScopedTrace .leaveInert 6
    (physicalSourceAssertionInitial context state ledger scannerAfter index
      cursor assertion)
    (physicalSourceAssertionDispatched context state ledger scannerAfter index
      cursor assertion)
  traceSteps : trace.steps = 6
  nativeTypeTrace : RuleScopedNativeTypeTrace .leaveInert 6
    (physicalSourceAssertionInitial context state ledger scannerAfter index
      cursor assertion)
    (physicalSourceAssertionDispatched context state ledger scannerAfter index
      cursor assertion)
  resultListNodup :
    (physicalSourceAssertionDispatched context state ledger scannerAfter index
      cursor assertion).Nodup
  resultMorkNodup : MorkSupportNodup
    (physicalSourceAssertionDispatched context state ledger scannerAfter index
      cursor assertion)

/-- Assemble the complete six-transition launch-to-dispatch segment from the
source request and the compact-key uniqueness of its initial physical space. -/
def physical_source_assertion_launch_to_dispatch_segment
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence} {index cursor : Nat}
    {assertion : SourceAssertion}
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion)
    (listNodup :
      (physicalSourceAssertionInitial context state ledger scannerAfter index
        cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (physicalSourceAssertionInitial context state ledger scannerAfter index
        cursor assertion)) :
    PhysicalSourceAssertionLaunchToDispatchSegment context state ledger
      scannerBefore scannerAfter occurrence index cursor assertion := by
  have launchStep := sourceDecoratedAssertionBridgeReadySpace_steps context
    state ledger scannerAfter index cursor assertion
  have ready := sourceAssertionBridgeLaunchResult_drain_ready context state
    ledger scannerAfter index cursor assertion listNodup morkNodup
  have drain := sourceAssertionBridgeLaunchResult_physical_drain context state
    ledger scannerAfter index cursor assertion listNodup morkNodup
  have launchBridge := sourceAssertionBridgeLaunchResult_bridge_mem context
    state ledger scannerAfter index cursor assertion listNodup morkNodup
  have bridgeMember :=
    normalDispatchBridge_survives_physical_predecessor_drain
      (physicalSourceAssertionLaunched context state ledger scannerAfter index
        cursor assertion)
      (physicalSourceAssertionDrained context state ledger scannerAfter index
        cursor assertion)
      ready drain launchBridge
  have dispatchStep := normalDispatchBridge_steps_after_predecessor_drain
    (physicalSourceAssertionLaunched context state ledger scannerAfter index
      cursor assertion)
    (physicalSourceAssertionDrained context state ledger scannerAfter index
      cursor assertion)
    ready drain bridgeMember
  let executionTrace : CRuleScopedTrace .leaveInert 6
      (physicalSourceAssertionInitial context state ledger scannerAfter index
        cursor assertion)
      (physicalSourceAssertionDispatched context state ledger scannerAfter index
        cursor assertion) :=
    .step launchStep
      (.step drain.proofStep
        (.step drain.lookupFaultStep
          (.step drain.cursorAssertionStep
            (.step drain.lookupAdvanceStep
              (.step dispatchStep .refl)))))
  exact
    { request := request
      sourceScannerStep := request.receipt.sourceStep
      assertionAuthored := request.authored
      heapRowSourceDerived :=
        sourceAssertionHeapRow_mem context.proofOwner state.heap index assertion
          request.heapLookup
      initialListNodup := listNodup
      initialMorkNodup := morkNodup
      launchStep := launchStep
      predecessorDrain := drain
      bridgeMember := bridgeMember
      dispatchStep := dispatchStep
      trace := executionTrace
      traceSteps := by rfl
      nativeTypeTrace := executionTrace.toNativeTypeTrace
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup _ _ drain.finalListNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup _ _ drain.finalMorkNodup }

/-- Negative control: a target assertion absent from the authenticated source
database cannot inhabit the source-bound physical segment. -/
theorem no_physical_source_assertion_launch_to_dispatch_of_not_authored
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {context : BoundaryContext} {state : MachineState source target}
    {ledger : NodeOccurrenceLedger state}
    {scannerBefore scannerAfter : ScannerBoundary}
    {occurrence : ByteOccurrence} {index cursor : Nat}
    {assertion : SourceAssertion}
    (notAuthored : assertion ∉ source.assertions) :
    ¬ Nonempty
      (PhysicalSourceAssertionLaunchToDispatchSegment context state ledger
        scannerBefore scannerAfter occurrence index cursor assertion) := by
  intro inhabited
  exact notAuthored inhabited.some.assertionAuthored

#print axioms physical_source_assertion_launch_to_dispatch_segment
#print axioms no_physical_source_assertion_launch_to_dispatch_of_not_authored

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionLaunchToDispatch
