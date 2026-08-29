import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAssertionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofScheduling

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- After an inert proof-cell probe, the frontier-fault probe is the exact
physical minimum of the remaining cursor interface. -/
theorem select_cursor_fault_after_proof_probe :
    selectNextScheduled
        [compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] =
      some compressedHeapLookupFaultDirective := by
  have advanceDoesNotPreempt :
      lexLt (SchedulerKey.key compressedHeapLookupAdvanceDirective)
        (SchedulerKey.key compressedHeapLookupFaultDirective) = false :=
    lexLt_asymm _ _ cursor_fault_preempts_cursor_advance
  unfold selectNextScheduled
  simp only [List.foldl_cons, cursor_fault_preempts_cursor_assertion,
    ↓reduceIte]
  simp only [advanceDoesNotPreempt, Bool.false_eq_true, ↓reduceIte,
    List.foldl_nil]

#print axioms select_cursor_fault_after_proof_probe

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofScheduling
