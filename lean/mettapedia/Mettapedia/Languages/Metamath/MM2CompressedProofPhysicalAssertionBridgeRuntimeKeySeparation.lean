import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation

/-!
# Runtime assertion-row key separation

Source-derived machine rows and compiler-owned opaque captures are physically
distinct from the captured normal-dispatch bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalHandoff
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK

private theorem additionalRows_shortNonExecHead
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈
      sourceAssertionAdditionalRows context state ledger scanner index
        assertion) :
    ∃ head,
      compressedDynamicRowHead? row = some head ∧
        0 < (morkUtf8Bytes head).length ∧
        (morkUtf8Bytes head).length < 64 ∧
        head ≠ "exec" := by
  rcases sourceAssertionAdditionalRows_head_cases context state ledger scanner
      index assertion member with scan | proof | assertionHeap | node |
        compactStack | normalStack | save
  · exact ⟨"mm-compressed-scan", scan, by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-heap-proof", proof, by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-heap-assertion", assertionHeap,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-node", node, by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-stack-cell", compactStack,
      by decide, by decide, by decide⟩
  · exact ⟨"mm-stack-cell", normalStack, by decide, by decide, by decide⟩
  · exact ⟨"mm-compressed-save-receipt", save,
      by decide, by decide, by decide⟩

theorem additionalRows_key_ne_bridge
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (assertion : SourceAssertion) {row : Atom}
    (member : row ∈
      sourceAssertionAdditionalRows context state ledger scanner index
        assertion) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  obtain ⟨head, headExact, headPositive, headBound, nonExec⟩ :=
    additionalRows_shortNonExecHead context state ledger scanner index assertion
      member
  exact dynamicRow_key_ne_normalDispatchBridge head headExact headPositive
    headBound nonExec

private theorem captureRows_shortNonExecHead {row : Atom}
    (member : row ∈ normalHandoffBridgeCaptureRows) :
    ∃ head,
      compressedDynamicRowHead? row = some head ∧
        0 < (morkUtf8Bytes head).length ∧
        (morkUtf8Bytes head).length < 64 ∧
        head ≠ "exec" := by
  simp only [normalHandoffBridgeCaptureRows, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with loader | finish
  · exact loader ▸ ⟨"mm-internal-compressed-normal-handoff-loader", rfl,
      by decide, by decide, by decide⟩
  · exact finish ▸ ⟨"mm-internal-compressed-normal-handoff-finish", rfl,
      by decide, by decide, by decide⟩

theorem captureRows_key_ne_bridge {row : Atom}
    (member : row ∈ normalHandoffBridgeCaptureRows) :
    morkSupportKey row ≠ morkSupportKey compressedNormalDispatchBridgeRule := by
  obtain ⟨head, headExact, headPositive, headBound, nonExec⟩ :=
    captureRows_shortNonExecHead member
  exact dynamicRow_key_ne_normalDispatchBridge head headExact headPositive
    headBound nonExec

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSourceKeySeparation
