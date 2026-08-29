import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Cursor zero has not reached frontier one, so the first fault probe is
inert and consumed by the ordinary scheduler. -/
theorem lookup_fault_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterTerminal =
      some lookupFaultAfterProbe := by
  decide +kernel

#print axioms lookup_fault_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary
