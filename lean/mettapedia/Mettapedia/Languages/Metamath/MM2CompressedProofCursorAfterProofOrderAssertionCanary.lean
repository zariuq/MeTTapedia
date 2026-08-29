import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_fault_preempts_cursor_assertion :
    lexLt (SchedulerKey.key compressedHeapLookupFaultDirective)
        (SchedulerKey.key compressedAssertionLaunchDirective) = true := by
  decide +kernel

#print axioms cursor_fault_preempts_cursor_assertion

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorAfterProofOrderAssertionCanary
