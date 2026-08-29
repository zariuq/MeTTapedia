import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- No proof-valued heap row exists at the first-free frontier. -/
theorem lookup_fault_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupFaultAfterAdvance =
      some lookupFaultAfterProofProbe := by
  decide +kernel

#print axioms lookup_fault_proof_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary
