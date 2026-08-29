import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderFinishCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The exact header-end witness releases compact body scanning. -/
theorem exact_header_end_releases_body_scanner :
    bodyControl ∈
      (cFireReflectiveSourceExecFact (finishProgram 0)
        compressedHeaderFinishDirective) := by
  decide +kernel

/-- A mismatched header end cannot release the body scanner. -/
theorem wrong_header_end_cannot_release_body_scanner :
    bodyControl ∉
      (cFireReflectiveSourceExecFact (finishProgram 1)
        compressedHeaderFinishDirective) := by
  decide +kernel

#print axioms exact_header_end_releases_body_scanner
#print axioms wrong_header_end_cannot_release_body_scanner

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderFinishCanary
