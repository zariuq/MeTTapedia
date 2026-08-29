import Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordPrefixProbeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- `A` is terminal, so the reloaded prefix handler is tried and remains
inert before terminal decoding. -/
theorem cross_word_prefix_probe_selected :
    cReflectiveSourceWorkQueueStep .leaveInert
        compressedCrossWordAfterAdvance =
      some compressedCrossWordAfterPrefixProbe := by
  decide +kernel

#print axioms cross_word_prefix_probe_selected

end Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordPrefixProbeCanary
