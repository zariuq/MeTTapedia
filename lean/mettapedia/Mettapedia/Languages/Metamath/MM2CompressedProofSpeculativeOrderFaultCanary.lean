import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderFaultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem direct_proof_preempts_cursor_fault :
    lexLt (SchedulerKey.key speculativeDirectProofDirective)
        (SchedulerKey.key compressedHeapLookupFaultDirective) = true := by
  rfl

#print axioms direct_proof_preempts_cursor_fault

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderFaultCanary
