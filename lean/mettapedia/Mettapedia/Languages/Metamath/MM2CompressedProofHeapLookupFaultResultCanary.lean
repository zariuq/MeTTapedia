import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultResultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

theorem lookup_frontier_fault_is_exclusive :
    missingOneFault ∈ lookupFaultAfterFault ∧
      resolvedStackCell ∉ lookupFaultAfterFault := by
  decide +kernel

#print axioms lookup_frontier_fault_is_exclusive

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupFaultResultCanary
