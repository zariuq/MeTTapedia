import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupWrongOwnerCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem speculative_wrong_owner_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert directWrongOwnerProofProgram =
      some directWrongOwnerProofAfter := by
  decide +kernel

theorem speculative_missing_assertion_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert directMissingAssertionProgram =
      some directMissingAssertionAfter := by
  decide +kernel

/-- Neither heterogeneous direct probe invents a proof stack cell.  Composition
of direct-probe exhaustion with the retained cursor path is a separate theorem
obligation. -/
theorem speculative_nonhits_are_exclusive :
    resolvedStackCell ∉ directWrongOwnerProofAfter ∧
      resolvedStackCell ∉ directMissingAssertionAfter := by
  exact ⟨by decide +kernel, by decide +kernel⟩

#print axioms speculative_wrong_owner_proof_probe_selected
#print axioms speculative_missing_assertion_probe_selected
#print axioms speculative_nonhits_are_exclusive

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupWrongOwnerCanary
