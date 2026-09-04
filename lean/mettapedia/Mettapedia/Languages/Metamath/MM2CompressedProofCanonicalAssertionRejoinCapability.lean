import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionExecutableFrameCapability

/-!
# Assertion-rejoin capability in the canonical decorated frame

The canonical assertion frame contains exactly one assertion-rejoin carrier.
Its payload is the admitted rejoin rule; supported directives and ordinary
data rows cannot impersonate that carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionRejoinCapability

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionExecutableFrameCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

private theorem direct_rule_not_rejoin :
    decodeCompressedExecutableCapture decoratedDirectAssertionDirective.atom =
      none :=
  decodeCompressedExecutableCapture_eq_none_of_supported
    extract_decoratedDirectAssertionRule_exact

private theorem cursor_rule_not_rejoin :
    decodeCompressedExecutableCapture decoratedCursorAssertionDirective.atom =
      none :=
  decodeCompressedExecutableCapture_eq_none_of_supported
    extract_decoratedCursorAssertionRule_exact

private theorem proof_rule_not_rejoin :
    decodeCompressedExecutableCapture compressedProofStepDirective.atom =
      none :=
  decodeCompressedExecutableCapture_eq_none_of_supported
    extract_compressedProofStepRule_exact

private theorem fault_rule_not_rejoin :
    decodeCompressedExecutableCapture
      compressedHeapLookupFaultDirective.atom = none :=
  decodeCompressedExecutableCapture_eq_none_of_supported
    extract_compressedHeapLookupFaultRule_exact

private theorem advance_rule_not_rejoin :
    decodeCompressedExecutableCapture
      compressedHeapLookupAdvanceDirective.atom = none :=
  decodeCompressedExecutableCapture_eq_none_of_supported
    extract_compressedHeapLookupAdvanceRule_exact

@[simp] theorem decode_rejoin_capture_row (context : DirectAssertionContext) :
    decodeCompressedExecutableCapture context.rejoinCaptureRow =
      some ⟨.runtime, "assertion-rejoin", compressedAssertionRejoinRule⟩ := by
  rfl

theorem canonicalDecoratedDirectAssertionSpace_rejoin_capabilities
    (context : DirectAssertionContext) :
    AssertionRejoinCapabilities compressedAssertionRejoinRule
      (canonicalDecoratedDirectAssertionSpace context) := by
  apply AssertionRejoinCapabilities.append
  · unfold decoratedDirectAssertionMatchSlice decoratedDirectAssertionDataSlice
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · exact direct_rule_not_rejoin
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    apply AssertionRejoinCapabilities.cons_expected
    · exact decode_rejoin_capture_row context
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · rfl
    exact AssertionRejoinCapabilities.nil _
  · unfold decoratedDirectAssertionSchedulerFrame
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · exact proof_rule_not_rejoin
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · exact cursor_rule_not_rejoin
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · exact fault_rule_not_rejoin
    apply AssertionRejoinCapabilities.cons_of_decode_none
    · exact advance_rule_not_rejoin
    exact AssertionRejoinCapabilities.nil _

#print axioms decode_rejoin_capture_row
#print axioms canonicalDecoratedDirectAssertionSpace_rejoin_capabilities

end Mettapedia.Languages.Metamath.MM2CompressedProofCanonicalAssertionRejoinCapability
