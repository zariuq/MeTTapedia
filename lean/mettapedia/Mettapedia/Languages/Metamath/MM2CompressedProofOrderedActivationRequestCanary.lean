import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationRequestCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

/-- The exact ordered theorem occurrence consumes its request and wrapped
header cursor, then starts verifier-inventory loading at position zero. -/
theorem exact_request_activates_compressed_verifier :
    canaryLoading 0 ∈ activationFinal ∧
      canaryRequest ∉ activationFinal ∧
      canaryPreparedHeaderControl ∉ activationFinal := by
  decide +kernel

/-- A request for another source occurrence cannot unwrap this theorem's
compressed header cursor. -/
theorem foreign_request_cannot_activate_compressed_verifier :
    canaryLoading 0 ∉ foreignActivationFinal ∧
      canaryPreparedHeaderControl ∈ foreignActivationFinal := by
  decide +kernel

#print axioms exact_request_activates_compressed_verifier
#print axioms foreign_request_cannot_activate_compressed_verifier

end Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationRequestCanary
