import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_hit_direct_scheduler_selected :
    selectNextScheduled
        (cSupportedSourceExecFacts speculativeHitAfterTerminal) =
      some speculativeDirectProofDirective := by
  exact select_direct_proof_of_supported_exact
    speculative_hit_after_terminal_supported_exact

theorem speculative_hit_direct_selected :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeHitAfterTerminal =
      some speculativeHitAfterDirect := by
  simp only [cReflectiveSourceWorkQueueStep,
    speculative_hit_direct_scheduler_selected, speculativeHitAfterDirect]

#print axioms speculative_hit_direct_scheduler_selected
#print axioms speculative_hit_direct_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary
