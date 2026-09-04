import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
import Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability

/-!
# Normal-bridge capability in the canonical assertion frame

Exactly one canonical carrier has the normal-dispatch bridge shape, and its
payload is the bridge authored by the ordered verifier presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalNormalBridgeCapability

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

@[simp] theorem decode_bridge_capture_row :
    decodeNormalDispatchBridgeCapture
      decoratedDirectAssertionBridgeCaptureRow =
        some compressedNormalDispatchBridgeRule := by
  rfl

private theorem direct_rule_not_bridge :
    decodeNormalDispatchBridgeCapture decoratedDirectAssertionDirective.atom =
      none := by
  exact decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_decoratedDirectAssertionRule_exact

private theorem cursor_rule_not_bridge :
    decodeNormalDispatchBridgeCapture decoratedCursorAssertionDirective.atom =
      none := by
  exact decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_decoratedCursorAssertionRule_exact

private theorem proof_rule_not_bridge :
    decodeNormalDispatchBridgeCapture compressedProofStepDirective.atom =
      none := by
  exact decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_compressedProofStepRule_exact

private theorem fault_rule_not_bridge :
    decodeNormalDispatchBridgeCapture compressedHeapLookupFaultDirective.atom =
      none := by
  exact decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_compressedHeapLookupFaultRule_exact

private theorem advance_rule_not_bridge :
    decodeNormalDispatchBridgeCapture
      compressedHeapLookupAdvanceDirective.atom = none := by
  exact decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_compressedHeapLookupAdvanceRule_exact

theorem canonicalDecoratedDirectAssertionSpace_bridge_capabilities
    (context : DirectAssertionContext) :
    NormalDispatchBridgeCapabilities compressedNormalDispatchBridgeRule
      (canonicalDecoratedDirectAssertionSpace context) := by
  apply NormalDispatchBridgeCapabilities.append
  · unfold decoratedDirectAssertionMatchSlice decoratedDirectAssertionDataSlice
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · exact direct_rule_not_bridge
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · rfl
    apply NormalDispatchBridgeCapabilities.cons_expected
    · exact decode_bridge_capture_row
    exact NormalDispatchBridgeCapabilities.nil _
  · unfold decoratedDirectAssertionSchedulerFrame
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · exact proof_rule_not_bridge
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · exact cursor_rule_not_bridge
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · exact fault_rule_not_bridge
    apply NormalDispatchBridgeCapabilities.cons_of_decode_none
    · exact advance_rule_not_bridge
    exact NormalDispatchBridgeCapabilities.nil _

#print axioms canonicalDecoratedDirectAssertionSpace_bridge_capabilities

end Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalNormalBridgeCapability
