import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultSelectCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultResultCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultProofProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultSelectCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- When compact index one is the first-free heap frontier, the same decoded
`B` reaches an explicit fault along one state-threaded path. -/
theorem lookup_one_at_frontier_faults_continuously :
    CReflectiveReachable .leaveInert 5 lookupFaultProgram
      lookupFaultAfterFault :=
  .step lookup_fault_terminal_selected
    (.step lookup_fault_probe_selected
      (.step lookup_fault_advance_selected
        (.step lookup_fault_proof_probe_selected
          (.step lookup_frontier_fault_selected .refl))))

#print axioms lookup_one_at_frontier_faults_continuously

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultCanary
