import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalExecPrefixOrder

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem speculative_direct_proof_representable :
    MorkCompactRepresentable speculativeDirectProofDirective.atom :=
  morkCompactRepresentable_of_isSome (by decide +kernel)

theorem speculative_direct_proof_scheduler_prefix :
    ∃ rest,
      SchedulerKey.key speculativeDirectProofDirective =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "00" ++
          compactSymbolBytes "mm-compressed-direct-0-proof" ++ rest := by
  change ∃ rest,
    totalMorkCompactKey speculativeDirectProofDirective.atom =
      [4, 196, 101, 120, 101, 99, 2] ++
        compactSymbolBytes "00" ++
        compactSymbolBytes "mm-compressed-direct-0-proof" ++ rest
  obtain ⟨input, output, surface⟩ :
      ExecSurfaceAt speculativeDirectProofDirective.atom
        speculativeDirectProofDirective.loc := by
    exact ⟨_, _, rfl⟩
  exact
    totalMorkCompactExec_location_prefix
      "00" "mm-compressed-direct-0-proof" input output surface (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      speculative_direct_proof_representable

theorem direct_proof_preempts_cursor_proof :
    lexLt (SchedulerKey.key speculativeDirectProofDirective)
        (SchedulerKey.key compressedProofStepDirective) = true := by
  rfl

#print axioms direct_proof_preempts_cursor_proof
#print axioms speculative_direct_proof_representable
#print axioms speculative_direct_proof_scheduler_prefix

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
