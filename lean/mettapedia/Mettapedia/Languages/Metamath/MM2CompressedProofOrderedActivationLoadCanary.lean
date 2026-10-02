import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationLoadCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

/-- One inventory transition transports the exact opaque rule value and moves
the occurrence-indexed cursor to its declared successor.  The stored code is
not made into a live executable before the dispatch phase. -/
theorem inventory_loads_exact_opaque_rule :
    compressedDispatchRuleRow canaryOpaqueRule ∈ loadFinal ∧
      canaryLoading 1 ∈ loadFinal ∧ canaryLoading 0 ∉ loadFinal ∧
      canaryOpaqueRule ∉ loadFinal := by
  decide +kernel

#print axioms inventory_loads_exact_opaque_rule

end Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationLoadCanary
