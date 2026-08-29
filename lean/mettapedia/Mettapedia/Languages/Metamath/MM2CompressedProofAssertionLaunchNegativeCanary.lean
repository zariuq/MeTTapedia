import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchNegativeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- A heap assertion row without its admitted assertion header cannot launch
the shared assertion kernel. -/
theorem assertion_without_header_cannot_launch :
    normalControl ∉
      cFireReflectiveSourceExecFact (launchProgram.erase assertionHeader)
        compressedAssertionLaunchDirective := by
  decide +kernel

#print axioms assertion_without_header_cannot_launch

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchNegativeCanary
