import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitAdvanceCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResolveCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem lookup_hit_after_advance_supported_exact :
    cSupportedSourceExecFacts lookupHitAfterAdvance =
      [compressedHeapLookupAdvanceDirective, compressedHeapLookupFaultDirective,
       compressedProofStepDirective, compressedAssertionLaunchDirective] := by
  decide +kernel

theorem lookup_hit_resolve_selected :
    cReflectiveSourceWorkQueueStep .leaveInert lookupHitAfterAdvance =
      some lookupHitAfterResolve := by
  exact lookup_step_of_selected lookupHitAfterAdvance compressedProofStepDirective
    (Eq.trans (congrArg selectNextScheduled lookup_hit_after_advance_supported_exact)
      lookup_select_fault_initial_proof)

#print axioms lookup_hit_resolve_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResolveCanary
