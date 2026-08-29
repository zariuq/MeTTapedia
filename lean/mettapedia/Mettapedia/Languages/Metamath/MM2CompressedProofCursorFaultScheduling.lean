import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultScheduling

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAdvanceCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- The ordinary proof-cell cursor probe is the exact physical minimum of the
four-rule lookup interface. -/
theorem select_cursor_proof_from_lookup_interface :
    selectNextScheduled
        [compressedProofStepDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] =
      some compressedProofStepDirective := by
  have assertionDoesNotPreempt :
      lexLt (SchedulerKey.key compressedAssertionLaunchDirective)
        (SchedulerKey.key compressedProofStepDirective) = false :=
    lexLt_asymm _ _ cursor_proof_preempts_cursor_assertion
  have faultDoesNotPreempt :
      lexLt (SchedulerKey.key compressedHeapLookupFaultDirective)
        (SchedulerKey.key compressedProofStepDirective) = false :=
    lexLt_asymm _ _ cursor_proof_preempts_cursor_fault
  have advanceDoesNotPreempt :
      lexLt (SchedulerKey.key compressedHeapLookupAdvanceDirective)
        (SchedulerKey.key compressedProofStepDirective) = false :=
    lexLt_asymm _ _ cursor_proof_preempts_cursor_advance
  unfold selectNextScheduled
  simp only [List.foldl_cons, assertionDoesNotPreempt, Bool.false_eq_true,
    ↓reduceIte]
  simp only [faultDoesNotPreempt, Bool.false_eq_true, ↓reduceIte]
  simp only [advanceDoesNotPreempt, Bool.false_eq_true, ↓reduceIte,
    List.foldl_nil]

#print axioms select_cursor_proof_from_lookup_interface

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultScheduling
