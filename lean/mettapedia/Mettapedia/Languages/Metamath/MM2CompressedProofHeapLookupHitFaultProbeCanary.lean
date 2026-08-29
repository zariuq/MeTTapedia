import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
/-- Resolving an existing entry below the frontier produces no missing-reference
fault. -/
theorem valid_lookup_has_no_missing_reference_fault :
    missingOneFault ∉ lookupHitAfterResolve := by
  decide +kernel

#print axioms valid_lookup_has_no_missing_reference_fault

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitFaultProbeCanary
