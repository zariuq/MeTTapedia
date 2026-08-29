import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

/-- An explicit assertion is a suspended operation: loading it allocates a
heap entry but no proof node and does not advance the node counter. -/
theorem assertion_load_advances_heap_without_allocating_node :
    assertionHeap ∈ assertionFinal ∧
      machine 1 0 0 ∈ assertionFinal ∧
      mandatoryNode ∉ assertionFinal := by
  decide +kernel

#print axioms assertion_load_advances_heap_without_allocating_node

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderAssertionCanary
