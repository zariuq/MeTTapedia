import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-- Returning from the shared normal assertion kernel restores both the
compact scanner state and its exact verifier-owned continuation rules. -/
theorem assertion_return_restores_compact_scanner :
    resumedScan ∈ resumeFinal ∧
      compressedPrefixRule ∈ resumeFinal ∧
      compressedAssertionLaunchRule ∈ resumeFinal ∧
      compressedAcceptRule ∈ resumeFinal := by
  decide +kernel

#print axioms assertion_return_restores_compact_scanner

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCanary
