import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordResultCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

theorem cross_word_result_is_compact_twenty :
    canaryCodeTwentyPending ∈ compressedCrossWordAfterTerminal := by
  decide +kernel

#print axioms cross_word_result_is_compact_twenty

end Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordResultCanary
