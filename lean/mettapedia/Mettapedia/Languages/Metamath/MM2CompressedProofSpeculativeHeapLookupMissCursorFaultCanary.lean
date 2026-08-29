import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorProofCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultScheduling

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorFaultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- At cursor zero, frontier one has not yet been reached, so the ordinary
missing-reference fault probe is inert. -/
theorem speculative_miss_cursor_fault_no_matches :
    cmatchInputSpec []
        (compressedHeapLookupFaultDirective.atom ::
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
              speculativeDirectAssertionDirective)
            compressedProofStepDirective).erase
              compressedHeapLookupFaultDirective.atom)
        compressedHeapLookupFaultDirective.rule.input = [] := by
  decide +kernel

/-- Erasing proof then fault from the ordinary four-rule cursor interface
leaves assertion launch ahead of cursor advance. -/
theorem speculative_miss_assertion_selected_after_cursor_fault_erasure :
    selectNextScheduled
        (([compressedProofStepDirective, compressedAssertionLaunchDirective,
           compressedHeapLookupFaultDirective,
           compressedHeapLookupAdvanceDirective].erase
            compressedProofStepDirective).erase
              compressedHeapLookupFaultDirective) =
      some compressedAssertionLaunchDirective := by
  rw [List.erase_cons_head]
  have faultErase :
      [compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective].erase
          compressedHeapLookupFaultDirective =
        [compressedAssertionLaunchDirective,
         compressedHeapLookupAdvanceDirective] := by
    decide +kernel
  rw [faultErase]
  exact select_cursor_assertion_after_fault_probe

#print axioms speculative_miss_cursor_fault_no_matches
#print axioms speculative_miss_assertion_selected_after_cursor_fault_erasure

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorFaultCanary
