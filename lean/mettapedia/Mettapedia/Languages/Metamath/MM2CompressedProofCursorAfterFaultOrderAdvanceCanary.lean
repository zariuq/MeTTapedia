import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultOrderAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_assertion_preempts_cursor_advance :
    lexLt (SchedulerKey.key compressedAssertionLaunchDirective)
        (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true := by
  decide +kernel

#print axioms cursor_assertion_preempts_cursor_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterFaultOrderAdvanceCanary
