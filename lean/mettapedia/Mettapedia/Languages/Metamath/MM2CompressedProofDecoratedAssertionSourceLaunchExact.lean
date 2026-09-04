import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionConsumption
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
import Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability

/-!
# Exact source-derived decorated assertion launch

This boundary combines source byte and heap authority, the actual
compiler-derived scheduled MM2 transition, exact publication of the normal
handoff, role-indexed capability origin, and consumption of obsolete compact
controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunchExact

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionConsumption
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Strong compact-to-normal launch boundary.  No assertion result is assumed
or emitted here; the normal verifier must still perform the assertion work. -/
structure SourceDecoratedAssertionExactLaunchSquare
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Prop where
  launch : SourceDecoratedAssertionLaunchSquare context state ledger
    scannerBefore scannerAfter occurrence index cursor assertion
  rejoinCapabilities :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
  bridgeCapabilities :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
  consumesPending :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    launchContext.pendingRow ∉
      cFireReflectiveSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion)
        decoratedDirectAssertionDirective
  consumesLookup :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    launchContext.lookupRow ∉
      cFireReflectiveSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion)
        decoratedDirectAssertionDirective
  consumesMachine :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    launchContext.machineRow ∉
      cFireReflectiveSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion)
        decoratedDirectAssertionDirective

theorem source_decorated_assertion_exact_launch_square
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion)
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion) :
    SourceDecoratedAssertionExactLaunchSquare context state ledger
      scannerBefore scannerAfter occurrence index cursor assertion := by
  let launchContext := directAssertionContextAtBoundary context state
    scannerAfter index cursor assertion
  let space := sourceDecoratedAssertionRequestSpace context state ledger
    scannerAfter index cursor assertion
  have matched : ExactDecoratedDirectAssertionLaunch launchContext space := by
    exact (source_decorated_assertion_launch_square context state ledger
      scannerBefore scannerAfter occurrence index cursor assertion
      request).exactMatcher
  have rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space := by
    exact sourceDecoratedAssertionRequestSpace_rejoin_capabilities context state
      ledger scannerAfter index cursor assertion
  have bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space := by
    exact sourceDecoratedAssertionRequestSpace_bridge_capabilities context state
      ledger scannerAfter index cursor assertion
  refine
    { launch := source_decorated_assertion_launch_square context state ledger
        scannerBefore scannerAfter occurrence index cursor assertion request
      rejoinCapabilities := rejoinCapabilities
      bridgeCapabilities := bridgeCapabilities
      consumesPending := ?_
      consumesLookup := ?_
      consumesMachine := ?_ }
  · exact decorated_direct_assertion_fire_consumes_pending launchContext space
      rejoinCapabilities bridgeCapabilities matched
  · exact decorated_direct_assertion_fire_consumes_lookup launchContext space
      rejoinCapabilities bridgeCapabilities matched
  · exact decorated_direct_assertion_fire_consumes_machine launchContext space
      rejoinCapabilities bridgeCapabilities matched

#print axioms source_decorated_assertion_exact_launch_square

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunchExact
