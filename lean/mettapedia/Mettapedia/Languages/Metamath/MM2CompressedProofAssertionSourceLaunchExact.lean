import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchConsumption

/-!
# Exact source-derived compressed assertion launch square

This module combines source byte decoding, semantic heap lookup, capability
origin, scheduled MM2 execution, OSLF native typing, publication of the normal
verifier interface, and consumption of every obsolete request control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceLaunchExact

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchConsumption
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Strong launch boundary before the normal assertion segment.  It neither
assumes nor publishes an assertion result: the emitted rows are precisely the
inputs and continuation needed by the independently verified normal machine. -/
structure SourceAssertionExactLaunchSquare
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Prop where
  launch : SourceAssertionLaunchSquare context state ledger scannerBefore
    scannerAfter occurrence index cursor assertion
  consumesPending :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    let space := sourceAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion
    launchContext.pendingRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective
  consumesLookup :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    let space := sourceAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion
    launchContext.lookupRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective
  consumesMachine :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    let space := sourceAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion
    launchContext.machineRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective

theorem source_assertion_exact_launch_square
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion)
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion) :
    SourceAssertionExactLaunchSquare context state ledger scannerBefore
      scannerAfter occurrence index cursor assertion := by
  let launchContext := directAssertionContextAtBoundary context state
    scannerAfter index cursor assertion
  let extra := sourceAssertionAdditionalRows context state ledger scannerAfter
    index assertion
  let space := sourceAssertionRequestSpace context state ledger scannerAfter
    index cursor assertion
  have capabilities := sourceAssertionRequestSpace_capabilities context state
    ledger scannerAfter index cursor assertion
  have matched : ExactDirectAssertionLaunch launchContext space := by
    exact canonical_exact_direct_assertion_launch_append launchContext extra
  refine
    { launch := source_assertion_launch_square context state ledger scannerBefore
        scannerAfter occurrence index cursor assertion request
      consumesPending := ?_
      consumesLookup := ?_
      consumesMachine := ?_ }
  · exact direct_assertion_fire_consumes_pending launchContext space
      capabilities matched
  · exact direct_assertion_fire_consumes_lookup launchContext space
      capabilities matched
  · exact direct_assertion_fire_consumes_machine launchContext space
      capabilities matched

#print axioms source_assertion_exact_launch_square

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceLaunchExact
