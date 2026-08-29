import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissCursorAdvanceStepCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierProofStepCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- At the first-free heap frontier there is still no proof-valued cell, so
the reloaded proof probe is consumed without resolving the request. -/
theorem speculative_miss_frontier_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeMissAfterAdvance =
      some speculativeMissAfterFrontierProofProbe := by
  decide +kernel

#print axioms speculative_miss_frontier_proof_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFrontierProofStepCanary
