import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitFaultProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResolveCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResultCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitFaultProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResolveCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A decoded `B` walks from compact heap cursor zero to entry one and pushes
that entry's exact proof-node identity along one state-threaded path. -/
theorem lookup_one_resolves_continuously :
    CReflectiveReachable .leaveInert 4 lookupHitProgram
      lookupHitAfterResolve :=
  .step lookup_hit_terminal_selected
    (.step lookup_hit_probe_selected
      (.step lookup_hit_advance_selected
        (.step lookup_hit_resolve_selected .refl)))

#print axioms lookup_one_resolves_continuously

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitCanary
