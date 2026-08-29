import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem direct_proof_preempts_cursor_advance :
    lexLt (SchedulerKey.key speculativeDirectProofDirective)
        (SchedulerKey.key compressedHeapLookupAdvanceDirective) = true := by
  rfl

#print axioms direct_proof_preempts_cursor_advance

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAdvanceCanary
