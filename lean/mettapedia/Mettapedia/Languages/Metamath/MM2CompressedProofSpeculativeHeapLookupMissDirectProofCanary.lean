import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectProofCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_miss_direct_proof_scheduler_selected :
    selectNextScheduled
        (cSupportedSourceExecFacts speculativeMissAfterTerminal) =
      some speculativeDirectProofDirective :=
  select_direct_proof_of_supported_exact
    speculative_miss_after_terminal_supported_exact

theorem speculative_miss_direct_proof_selected :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeMissAfterTerminal =
      some speculativeMissAfterDirectProof := by
  simp only [cReflectiveSourceWorkQueueStep,
    speculative_miss_direct_proof_scheduler_selected,
    speculativeMissAfterDirectProof]

/-- A direct proof probe with no owner-matching heap row is consumed without
altering the lookup request or its pending stack step. -/
theorem speculative_miss_direct_proof_is_inert :
    directLookupOne ∈ speculativeMissAfterDirectProof ∧
      directStepPending ∈ speculativeMissAfterDirectProof := by
  decide +kernel

#print axioms speculative_miss_direct_proof_scheduler_selected
#print axioms speculative_miss_direct_proof_selected
#print axioms speculative_miss_direct_proof_is_inert

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectProofCanary
