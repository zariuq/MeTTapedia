import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- At cursor zero the proof handler is tried but cannot resolve target one. -/
theorem lookup_hit_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterTerminal =
      some lookupHitAfterProofProbe := by
  decide +kernel

#print axioms lookup_hit_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
