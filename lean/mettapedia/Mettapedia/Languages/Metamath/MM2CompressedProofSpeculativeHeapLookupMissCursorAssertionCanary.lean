import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorFaultCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterAssertionScheduling

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterAssertionScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The foreign-owner heap row is neither proof-valued nor assertion-valued
for the requested proof, so the ordinary assertion cursor probe is inert. -/
theorem speculative_miss_cursor_assertion_no_matches :
    cmatchInputSpec []
        (compressedAssertionLaunchDirective.atom ::
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact
              (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
                speculativeDirectAssertionDirective)
              compressedProofStepDirective)
            compressedHeapLookupFaultDirective).erase
              compressedAssertionLaunchDirective.atom)
        compressedAssertionLaunchDirective.rule.input = [] := by
  decide +kernel

/-- After proof, fault, and assertion probes are erased, cursor advance is
the sole remaining lookup directive. -/
theorem speculative_miss_advance_selected_after_cursor_probes :
    selectNextScheduled
        ((([compressedProofStepDirective, compressedAssertionLaunchDirective,
            compressedHeapLookupFaultDirective,
            compressedHeapLookupAdvanceDirective].erase
              compressedProofStepDirective).erase
                compressedHeapLookupFaultDirective).erase
                  compressedAssertionLaunchDirective) =
      some compressedHeapLookupAdvanceDirective := by
  rw [List.erase_cons_head]
  have faultErase :
      [compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective].erase
          compressedHeapLookupFaultDirective =
        [compressedAssertionLaunchDirective,
         compressedHeapLookupAdvanceDirective] := by
    decide +kernel
  rw [faultErase, List.erase_cons_head]
  exact select_cursor_advance_after_assertion_probe

#print axioms speculative_miss_cursor_assertion_no_matches
#print axioms speculative_miss_advance_selected_after_cursor_probes

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAssertionCanary
