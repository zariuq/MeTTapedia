import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalExecPrefixOrder

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem speculative_direct_assertion_representable :
    MorkCompactRepresentable speculativeDirectAssertionDirective.atom :=
  morkCompactRepresentable_of_isSome (by decide +kernel)

theorem speculative_direct_assertion_scheduler_prefix :
    ∃ rest,
      SchedulerKey.key speculativeDirectAssertionDirective =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "00" ++
          compactSymbolBytes "mm-compressed-direct-1-assertion" ++ rest := by
  change ∃ rest,
    totalMorkCompactKey speculativeDirectAssertionDirective.atom =
      [4, 196, 101, 120, 101, 99, 2] ++
        compactSymbolBytes "00" ++
        compactSymbolBytes "mm-compressed-direct-1-assertion" ++ rest
  obtain ⟨input, output, surface⟩ :
      ExecSurfaceAt speculativeDirectAssertionDirective.atom
        speculativeDirectAssertionDirective.loc := by
    exact ⟨_, _, rfl⟩
  exact
    totalMorkCompactExec_location_prefix
      "00" "mm-compressed-direct-1-assertion" input output surface (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      speculative_direct_assertion_representable

theorem direct_proof_preempts_direct_assertion :
    lexLt (SchedulerKey.key speculativeDirectProofDirective)
        (SchedulerKey.key speculativeDirectAssertionDirective) = true := by
  obtain ⟨proofRest, proofPrefix⟩ :=
    speculative_direct_proof_scheduler_prefix
  obtain ⟨assertionRest, assertionPrefix⟩ :=
    speculative_direct_assertion_scheduler_prefix
  rw [proofPrefix, assertionPrefix]
  rfl

theorem direct_assertion_does_not_preempt_direct_proof :
    lexLt (SchedulerKey.key speculativeDirectAssertionDirective)
        (SchedulerKey.key speculativeDirectProofDirective) = false := by
  exact lexLt_asymm _ _ direct_proof_preempts_direct_assertion

#print axioms speculative_direct_assertion_representable
#print axioms speculative_direct_assertion_scheduler_prefix
#print axioms direct_proof_preempts_direct_assertion
#print axioms direct_assertion_does_not_preempt_direct_proof

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary
