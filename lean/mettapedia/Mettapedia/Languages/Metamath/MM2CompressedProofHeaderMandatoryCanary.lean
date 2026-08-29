import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderMandatoryCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

/-- Loading a mandatory hypothesis uses the same fresh node identity for the
node record and the corresponding heap entry, then advances both counters. -/
theorem mandatory_load_allocates_same_node_and_heap_identity :
    mandatoryNode ∈ mandatoryFinal ∧
      mandatoryHeap ∈ mandatoryFinal ∧
      mandatoryMarker ∈ mandatoryFinal ∧
      machine 1 1 0 ∈ mandatoryFinal ∧
      headerControl 1 ∈ mandatoryFinal := by
  decide +kernel

#print axioms mandatory_load_allocates_same_node_and_heap_identity

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderMandatoryCanary
