import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Exact normal-bridge scheduler membership

An exact resident normal-dispatch bridge row decodes to the corresponding
scheduler candidate.  Keeping this representation boundary opaque prevents
downstream scheduler proofs from unfolding the large executable row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalBridgeSupportedMembership

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Exact physical membership of the bridge row yields exact membership of its
decoded scheduler directive. -/
theorem normalDispatchBridge_supported_of_mem {space : List Atom}
    (member : compressedNormalDispatchBridgeRule ∈ space) :
    compressedNormalDispatchBridgeDirective ∈
      cSupportedSourceExecFacts space := by
  exact sourceExecFact_mem_supported_of_atom_mem member
    extract_compressedNormalDispatchBridgeRule_exact

#print axioms normalDispatchBridge_supported_of_mem

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalBridgeSupportedMembership
