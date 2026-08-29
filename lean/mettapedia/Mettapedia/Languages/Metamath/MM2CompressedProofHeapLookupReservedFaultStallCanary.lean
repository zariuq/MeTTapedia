import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultStallCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The concrete Lean runner becomes quiescent immediately after selecting
the advance directive, rather than reaching either a hit or the explicit
frontier fault. -/
theorem reserved_fault_advance_reaches_quiescent_state :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterAdvance = none := by
  decide +kernel

theorem reserved_fault_advance_emits_no_frontier_fault :
    missingOneFault ∉ lookupReservedFaultAfterAdvance := by
  decide +kernel

#print axioms reserved_fault_advance_reaches_quiescent_state
#print axioms reserved_fault_advance_emits_no_frontier_fault

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultStallCanary
