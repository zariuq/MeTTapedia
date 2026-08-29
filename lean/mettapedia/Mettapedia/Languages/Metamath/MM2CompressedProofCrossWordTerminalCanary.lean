import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordTerminalCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem cross_word_terminal_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        compressedCrossWordAfterPrefixProbe =
      some compressedCrossWordAfterTerminal := by
  decide +kernel

#print axioms cross_word_terminal_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordTerminalCanary
