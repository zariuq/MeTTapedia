import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPublication
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension

/-!
# Source-derived launch through the decorated ordered verifier

The scanner receipt and semantic heap lookup determine the compact assertion
request.  The actual compiler-produced direct assertion handler then performs
one scheduled MM2 step whose exact matcher publishes the normal assertion
interface and its normal-dispatch bridge.  Source-derived passive rows cannot
alter the scheduler inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPublication
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def sourceDecoratedAssertionRequestSpace
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) : List Atom :=
  canonicalDecoratedDirectAssertionSpace
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) ++
    sourceAssertionAdditionalRows context state ledger scanner index assertion

/-- Membership in the source-derived assertion request decomposes at the
canonical assertion/data boundary without exposing either representation. -/
theorem mem_sourceDecoratedAssertionRequestSpace_iff
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) (row : Atom) :
    row ∈ sourceDecoratedAssertionRequestSpace context state ledger scanner
        index cursor assertion ↔
      row ∈ canonicalDecoratedDirectAssertionSpace
          (directAssertionContextAtBoundary context state scanner index cursor
            assertion) ∨
        row ∈ sourceAssertionAdditionalRows context state ledger scanner index
          assertion := by
  simp [sourceDecoratedAssertionRequestSpace]

#print axioms mem_sourceDecoratedAssertionRequestSpace_iff

/-- Source-derived assertion launch through the actual decorated compiler
product.  The witness stores no assertion result: only source authority, an
exact target matcher, and the scheduled transition generated from it. -/
structure SourceDecoratedAssertionLaunchSquare
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Prop where
  request : SourceAssertionRequest context state scannerBefore scannerAfter
    occurrence index assertion
  sourceScannerStep :
    SourceStep (.request occurrence scannerBefore.phase)
      (.outcome occurrence (.decoded [.step index] scannerAfter.phase))
  assertionAuthored : assertion ∈ source.assertions
  heapRowSourceDerived :
    sourceAssertionHeapRow (source := source) context.proofOwner index assertion ∈
      assertionHeapRows context.proofOwner state.heap
  compiledDirectRule :
    decoratedDirectAssertionRule ∈ decoratedSpeculativeBody.targetRules
  bridgeCarrierInPresentation :
    decoratedDirectAssertionBridgeCaptureRow ∈
      compressedSpeculativeOrderedVerifierExtensionProgram
  exactMatcher :
    ExactDecoratedDirectAssertionLaunch
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
  scheduled :
    cReflectiveSourceWorkQueueStep .leaveInert
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion) =
      some (cFireReflectiveSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion) decoratedDirectAssertionDirective)
  publishesNormalAndBridge :
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    ∀ row ∈ decoratedDirectAssertionLaunchRows launchContext,
      row ∈ cFireReflectiveSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion) decoratedDirectAssertionDirective
  nativeTarget :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (cFireReflectiveSourceExecFact
          (sourceDecoratedAssertionRequestSpace context state ledger
            scannerAfter index cursor assertion)
          decoratedDirectAssertionDirective)).pred

theorem source_decorated_assertion_launch_square
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion)
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion) :
    SourceDecoratedAssertionLaunchSquare context state ledger scannerBefore
      scannerAfter occurrence index cursor assertion where
  request := request
  sourceScannerStep := request.receipt.sourceStep
  assertionAuthored := request.authored
  heapRowSourceDerived :=
    sourceAssertionHeapRow_mem context.proofOwner state.heap index assertion
      request.heapLookup
  compiledDirectRule := decoratedDirectAssertionRule_mem_targetRules
  bridgeCarrierInPresentation :=
    decoratedDirectAssertionBridgeCaptureRow_mem_program
  exactMatcher := by
    exact canonical_exact_decorated_direct_assertion_launch_append
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
  scheduled := by
    exact canonicalDecoratedDirectAssertionSpace_append_steps
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
      (sourceAssertionAdditionalRows_no_supported context state ledger
        scannerAfter index assertion)
  publishesNormalAndBridge := by
    exact decorated_direct_assertion_fire_adds_launch_rows
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      (canonical_exact_decorated_direct_assertion_launch_append
        (directAssertionContextAtBoundary context state scannerAfter index
          cursor assertion)
        (sourceAssertionAdditionalRows context state ledger scannerAfter index
          assertion))
  nativeTarget := by
    apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
      .leaveInert _ _).2
    exact canonicalDecoratedDirectAssertionSpace_append_steps
      (directAssertionContextAtBoundary context state scannerAfter index cursor
        assertion)
      (sourceAssertionAdditionalRows context state ledger scannerAfter index
        assertion)
      (sourceAssertionAdditionalRows_no_supported context state ledger
        scannerAfter index assertion)

#print axioms source_decorated_assertion_launch_square

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
