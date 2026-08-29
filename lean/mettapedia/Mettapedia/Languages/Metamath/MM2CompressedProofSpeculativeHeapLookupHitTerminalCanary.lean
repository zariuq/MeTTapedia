import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

theorem speculative_hit_terminal_selected :
    cReflectiveSourceWorkQueueStep .leaveInert speculativeHitProgram =
      some speculativeHitAfterTerminal := by
  decide +kernel

/-- The first transition exposes exactly the six verifier rules needed by the
lookup phase.  This small interface receipt prevents later proofs from
normalizing the terminal transition again. -/
theorem speculative_hit_after_terminal_supported_exact :
    cSupportedSourceExecFacts speculativeHitAfterTerminal =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectProofDirective, speculativeDirectAssertionDirective] := by
  rfl

#print axioms speculative_hit_terminal_selected
#print axioms speculative_hit_after_terminal_supported_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
