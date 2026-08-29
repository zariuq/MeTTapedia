import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_proof_preempts_cursor_fault :
    lexLt (SchedulerKey.key compressedProofStepDirective)
        (SchedulerKey.key compressedHeapLookupFaultDirective) = true := by
  decide +kernel

#print axioms cursor_proof_preempts_cursor_fault

end Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultOrderProofCanary
