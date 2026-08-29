import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationFinishCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

/-- The exact inventory end releases the original compressed header cursor. -/
theorem exact_inventory_end_releases_header :
    canaryHeaderControl ∈ finishFinal ∧ canaryLoading 1 ∉ finishFinal := by
  decide +kernel

/-- An end marker for another inventory position cannot release the header. -/
theorem wrong_inventory_end_cannot_release_header :
    canaryHeaderControl ∉ wrongFinishFinal ∧
      canaryLoading 1 ∈ wrongFinishFinal := by
  decide +kernel

#print axioms exact_inventory_end_releases_header
#print axioms wrong_inventory_end_cannot_release_header

end Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationFinishCanary
