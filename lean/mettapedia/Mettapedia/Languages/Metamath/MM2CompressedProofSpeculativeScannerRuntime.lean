import Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin

/-!
# Compiler-bound speculative scanner runtime

The scanner inventory restored after a compressed assertion is not an
independent list of rule constants.  Every role-indexed capture is present in
the maintained speculative compiler target and is authorized by the
presentation derived from that same compiler result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeScannerRuntime

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSaveContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofScannerRuntimeInventory
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Finite compiler-artifact check for the complete assertion-resume capture
inventory. -/
def speculativeScannerRuntimeCaptureCoverage : Bool :=
  speculativeScannerRuntimeRuleBundle.captureRows.all fun row =>
    row ∈ baseCompiledPresentation.targetStaticRows

theorem speculativeScannerRuntimeCaptureCoverage_eq_true :
    speculativeScannerRuntimeCaptureCoverage = true := by
  decide +kernel

/-- Every resume capture is retained by the actual speculative compiler
artifact. -/
theorem speculativeScannerRuntimeCaptureRows_mem_target
    (row : Atom)
    (member : row ∈ speculativeScannerRuntimeRuleBundle.captureRows) :
    row ∈ baseCompiledPresentation.targetStaticRows := by
  have checked := speculativeScannerRuntimeCaptureCoverage_eq_true
  unfold speculativeScannerRuntimeCaptureCoverage at checked
  exact of_decide_eq_true ((List.all_eq_true.mp checked) row member)

/-- The compiler-derived capability map authorizes every capture restored by
assertion resume. -/
theorem speculativeScannerRuntimeCaptureRows_authorized :
    CompressedExecutableCapabilities speculativeBaseExecutablePresentation
      speculativeScannerRuntimeRuleBundle.captureRows := by
  intro carrier member
  exact speculative_target_static_rows_authorized carrier
    (speculativeScannerRuntimeCaptureRows_mem_target carrier member)

/-- Runtime payloads are static executable code, never source-machine rows. -/
theorem speculativeScannerRuntimePayload_static
    (row : Atom)
    (member : row ∈ speculativeScannerRuntimeRuleBundle.payloadRows) :
    isDynamicRow row = false := by
  simp only [ScannerRuntimeRuleBundle.payloadRows,
    speculativeScannerRuntimeRuleBundle, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.prefixStatic
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.terminalStatic
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.proofStatic
  · simp [isDynamicRow, dynamicRowHeads, compressedAssertionLaunchRule]
  · simp [isDynamicRow, dynamicRowHeads, compressedSaveRule]
  · simp [isDynamicRow, dynamicRowHeads, compressedWordAdvanceRule]
  · simp [isDynamicRow, dynamicRowHeads, compressedAcceptRule]
  · simp [isDynamicRow, dynamicRowHeads, compressedIncompleteRule]
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.invalidByteStatic
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.questionStatic
  · simpa [speculativeScannerRuntimeRuleBundle,
      speculativeSaveRuntimeRuleAuthority, speculativeSaveRuntimeRuleBundle,
      baseSaveRuntimeRuleBundle] using
      speculativeSaveRuntimeRuleAuthority.questionOpenFaultStatic
  · simp [isDynamicRow, dynamicRowHeads, compressedSaveFaultRule]

/-- The compiler-selected assertion-resume carriers have distinct physical
MORK support identities.  The finite check includes the transformed terminal
payload rather than inheriting duplicate freedom from the base inventory. -/
theorem speculativeScannerRuntimeCaptureRows_mork_nodup :
    MorkSupportNodup speculativeScannerRuntimeRuleBundle.captureRows := by
  unfold MorkSupportNodup
  decide +kernel

#print axioms speculativeScannerRuntimeCaptureCoverage_eq_true
#print axioms speculativeScannerRuntimeCaptureRows_mem_target
#print axioms speculativeScannerRuntimeCaptureRows_authorized
#print axioms speculativeScannerRuntimePayload_static
#print axioms speculativeScannerRuntimeCaptureRows_mork_nodup

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeScannerRuntime
