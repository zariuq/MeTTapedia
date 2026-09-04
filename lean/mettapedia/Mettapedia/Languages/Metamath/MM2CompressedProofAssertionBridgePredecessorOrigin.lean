import Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionPredecessorOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff

/-!
# Source assertion-workspace predecessor origin

The finite canonical assertion frame, source-derived passive display, scanner,
and normal-handoff captures jointly contain no additional pending or lookup
rows.  This is the source-relative premise used by the physical scheduler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionPredecessorOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

private theorem sourceAssertionAdditionalRows_predecessor_origin
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion)
    (launchContext : DirectAssertionContext) :
    AtomsWithin (AssertionPredecessorRowOrigin launchContext)
      (sourceAssertionAdditionalRows context state ledger scanner index
        assertion) := by
  intro atom member
  rcases sourceAssertionAdditionalRows_head_cases context state ledger scanner
      index assertion member with
    scan | heapProof | heapAssertion | node | compactStack | normalStack | save
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-scan" scan (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-heap-proof" heapProof (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-heap-assertion" heapAssertion (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-node" node (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-stack-cell" compactStack (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-stack-cell" normalStack (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head launchContext
      "mm-compressed-save-receipt" save (by decide) (by decide)

private theorem normalHandoffBridgeCaptureRows_predecessor_origin
    (context : DirectAssertionContext) :
    AtomsWithin (AssertionPredecessorRowOrigin context)
      normalHandoffBridgeCaptureRows := by
  intro atom member
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-internal-compressed-normal-handoff-loader" rfl
      (by decide) (by decide)
  · exact assertionPredecessorRowOrigin_of_other_head context
      "mm-internal-compressed-normal-handoff-finish" rfl
      (by decide) (by decide)

/-- In the complete source-derived assertion request, the pending and lookup
families each have exactly the row reconstructed from the source boundary.
Static executable shells and opaque captures cannot supply either family. -/
theorem sourceDecoratedAssertionBridgeReadySpace_predecessor_origin
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    let launchContext := directAssertionContextAtBoundary context state scanner
      index cursor assertion
    AtomsWithin (AssertionPredecessorRowOrigin launchContext)
      (@sourceDecoratedAssertionBridgeReadySpace source target context state
        ledger scanner index cursor assertion) := by
  dsimp only
  intro atom member
  simp only [sourceDecoratedAssertionBridgeReadySpace,
    sourceDecoratedAssertionRequestSpace, List.mem_append] at member
  rcases member with (canonical | additional) | capture
  · exact canonicalDecoratedDirectAssertionSpace_predecessor_origin
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) atom canonical
  · exact sourceAssertionAdditionalRows_predecessor_origin context state
      ledger scanner index assertion
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) atom additional
  · exact normalHandoffBridgeCaptureRows_predecessor_origin
      (directAssertionContextAtBoundary context state scanner index cursor
        assertion) atom capture

#print axioms sourceDecoratedAssertionBridgeReadySpace_predecessor_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgePredecessorOrigin
