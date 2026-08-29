import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultScheduling
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertScheduling

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofCursorFaultScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissDirectAssertionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-- Erasing the inert direct assertion probe from the exact five-rule
interface exposes the ordinary cursor proof probe next. -/
theorem speculative_miss_cursor_proof_selected_from_direct_interface :
    selectNextScheduled
        ([compressedProofStepDirective, compressedAssertionLaunchDirective,
          compressedHeapLookupFaultDirective,
          compressedHeapLookupAdvanceDirective,
          speculativeDirectAssertionDirective].erase
            speculativeDirectAssertionDirective) =
      some compressedProofStepDirective := by
  have eraseExact :
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective,
       compressedHeapLookupAdvanceDirective,
       speculativeDirectAssertionDirective].erase
          speculativeDirectAssertionDirective =
        [compressedProofStepDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective] := by
    decide +kernel
  rw [eraseExact]
  exact select_cursor_proof_from_lookup_interface

/-- The first ordinary proof-cell probe begins from the state produced by both
direct misses rather than from a separately reconstructed cursor fixture. -/
theorem speculative_miss_cursor_proof_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
          speculativeDirectAssertionDirective) =
      some
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact speculativeMissAfterDirectProof
            speculativeDirectAssertionDirective)
          compressedProofStepDirective) := by
  exact cReflectiveSourceWorkQueueStep_after_inert
    speculativeMissAfterDirectProof speculativeDirectAssertionDirective
    compressedProofStepDirective
    [compressedProofStepDirective, compressedAssertionLaunchDirective,
     compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
     speculativeDirectAssertionDirective]
    extract_speculativeDirectAssertionDirective_exact
    speculative_miss_direct_assertion_no_matches
    speculative_miss_after_direct_proof_supported_exact
    speculative_miss_cursor_proof_selected_from_direct_interface

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissFaultProbeCanary
