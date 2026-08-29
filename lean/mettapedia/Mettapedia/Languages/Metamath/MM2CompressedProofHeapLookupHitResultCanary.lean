import Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary

theorem lookup_one_pushes_exact_node :
    resolvedStackCell ∈ lookupHitAfterResolve := by
  decide +kernel

#print axioms lookup_one_pushes_exact_node

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupHitResultCanary
