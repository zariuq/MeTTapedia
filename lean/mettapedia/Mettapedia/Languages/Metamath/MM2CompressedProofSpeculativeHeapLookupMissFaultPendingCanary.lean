import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPendingCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

/-- The source-bound pending step survives the speculative probes and cursor
advance until the frontier fault consumes it. -/
theorem direct_step_pending_in_speculative_miss_fault_live_space :
    directStepPending ∈
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom := by
  decide +kernel

#print axioms direct_step_pending_in_speculative_miss_fault_live_space

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPendingCanary
