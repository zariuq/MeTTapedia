import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordAdvanceCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem cross_word_advance_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        compressedCrossWordTwentyProgram =
      some compressedCrossWordAfterAdvance := by
  decide +kernel

#print axioms cross_word_advance_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordAdvanceCanary
