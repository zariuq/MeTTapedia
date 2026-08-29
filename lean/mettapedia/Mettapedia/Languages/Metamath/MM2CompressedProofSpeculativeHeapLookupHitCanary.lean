import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitResultCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitDirectCanary

/-- The transformed terminal and its derived direct proof handler form one
continuous two-step execution: the first successor is literally the second
step's input. -/
theorem speculative_terminal_and_direct_hit_execute_continuously :
    Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.cReflectiveSourceWorkQueueStep
        .leaveInert speculativeHitProgram = some speculativeHitAfterTerminal ∧
      Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.cReflectiveSourceWorkQueueStep
        .leaveInert speculativeHitAfterTerminal = some speculativeHitAfterDirect :=
  ⟨speculative_hit_terminal_selected, speculative_hit_direct_selected⟩

#print axioms speculative_terminal_and_direct_hit_execute_continuously

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitCanary
