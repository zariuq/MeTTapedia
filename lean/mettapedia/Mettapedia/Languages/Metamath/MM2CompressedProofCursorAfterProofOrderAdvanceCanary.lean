import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_fault_preempts_cursor_advance :
    lexLt (SchedulerKey.key compressedHeapLookupFaultDirective)
        (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true := by
  decide +kernel

#print axioms cursor_fault_preempts_cursor_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAdvanceCanary
