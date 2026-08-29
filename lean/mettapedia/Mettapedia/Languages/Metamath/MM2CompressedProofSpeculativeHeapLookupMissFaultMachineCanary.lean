import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultMachineCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

/-- The heap-frontier machine state remains live until the fault handler
consumes it. -/
theorem machine_in_speculative_miss_fault_live_space :
    machineWithOneHeapEntry ∈
      speculativeMissAfterFrontierProofProbe.erase
        compressedHeapLookupFaultDirective.atom := by
  decide +kernel

#print axioms machine_in_speculative_miss_fault_live_space

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultMachineCanary
