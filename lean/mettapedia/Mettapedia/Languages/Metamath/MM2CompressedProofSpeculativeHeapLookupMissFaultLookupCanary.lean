import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultPendingCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultLookupCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultInputData

/-- Cursor advance produces the exact first-free frontier lookup subsequently
consumed by the fault handler. -/
theorem frontier_lookup_in_speculative_miss_fault_live_space :
    frontierLookupOne ∈
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom := by
  decide +kernel

#print axioms frontier_lookup_in_speculative_miss_fault_live_space

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultLookupCanary
