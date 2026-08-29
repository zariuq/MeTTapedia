import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultTerminalCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem reserved_fault_probe_scheduler :
    selectNextScheduled
        (cSupportedSourceExecFacts lookupReservedFaultAfterTerminal) =
      some compressedHeapLookupFaultDirective := by
  decide +kernel

theorem reserved_fault_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        lookupReservedFaultAfterTerminal =
      some lookupReservedFaultAfterProbe := by
  unfold cReflectiveSourceWorkQueueStep
  rw [reserved_fault_probe_scheduler]

#print axioms reserved_fault_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupReservedFaultProbeCanary
