import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_miss_terminal_selected :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeMissProgram =
      some speculativeMissAfterTerminal := by
  decide +kernel

/-- Data ownership changes matching, not the verifier inventory exposed by
the transformed terminal. -/
theorem speculative_miss_after_terminal_supported_exact :
    cSupportedSourceExecFacts speculativeMissAfterTerminal =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectProofDirective, speculativeDirectAssertionDirective] := by
  rfl

#print axioms speculative_miss_terminal_selected
#print axioms speculative_miss_after_terminal_supported_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupMissTerminalCanary
