import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalExecPrefixOrder

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
open Mettapedia.Languages.ProcessCalculi.MORK

theorem cursor_assertion_representable :
    MorkCompactRepresentable compressedAssertionLaunchDirective.atom :=
  morkCompactRepresentable_of_isSome (by decide +kernel)

theorem cursor_assertion_scheduler_prefix :
    ∃ rest,
      SchedulerKey.key compressedAssertionLaunchDirective =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes "08" ++
          compactSymbolBytes "mm-compressed-proof-step-assertion" ++ rest := by
  change ∃ rest,
    totalMorkCompactKey compressedAssertionLaunchDirective.atom =
      [4, 196, 101, 120, 101, 99, 2] ++
        compactSymbolBytes "08" ++
        compactSymbolBytes "mm-compressed-proof-step-assertion" ++ rest
  obtain ⟨input, output, surface⟩ :
      ExecSurfaceAt compressedAssertionLaunchDirective.atom
        compressedAssertionLaunchDirective.loc := by
    exact ⟨_, _, rfl⟩
  exact
    totalMorkCompactExec_location_prefix
      "08" "mm-compressed-proof-step-assertion" input output surface (by rfl)
      (by decide) (by decide) (by decide) (by decide)
      cursor_assertion_representable

theorem direct_proof_preempts_cursor_assertion :
    lexLt (SchedulerKey.key speculativeDirectProofDirective)
        (SchedulerKey.key compressedAssertionLaunchDirective) = true := by
  obtain ⟨directRest, directPrefix⟩ :=
    speculative_direct_proof_scheduler_prefix
  obtain ⟨assertionRest, assertionPrefix⟩ :=
    cursor_assertion_scheduler_prefix
  rw [directPrefix, assertionPrefix]
  rfl

#print axioms direct_proof_preempts_cursor_assertion
#print axioms cursor_assertion_representable
#print axioms cursor_assertion_scheduler_prefix

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary
