import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultOrderAdvanceCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultScheduling

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultOrderAdvanceCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem select_cursor_assertion_after_fault_probe :
    selectNextScheduled
        [compressedAssertionLaunchDirective,
         compressedHeapLookupAdvanceDirective] =
      some compressedAssertionLaunchDirective := by
  have advanceDoesNotPreempt :
      lexLt (SchedulerKey.key compressedHeapLookupAdvanceDirective)
        (SchedulerKey.key compressedAssertionLaunchDirective) = false :=
    lexLt_asymm _ _ cursor_assertion_preempts_cursor_advance
  unfold selectNextScheduled
  simp only [List.foldl_cons, advanceDoesNotPreempt, Bool.false_eq_true,
    ↓reduceIte, List.foldl_nil]

#print axioms select_cursor_assertion_after_fault_probe

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultScheduling
