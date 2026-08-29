import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_proof_preempts_cursor_assertion :
    lexLt (SchedulerKey.key compressedProofStepDirective)
        (SchedulerKey.key compressedAssertionLaunchDirective) = true := by
  decide +kernel

#print axioms cursor_proof_preempts_cursor_assertion

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderAssertionCanary
