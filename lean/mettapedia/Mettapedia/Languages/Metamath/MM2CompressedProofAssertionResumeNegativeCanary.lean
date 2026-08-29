import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeNegativeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- A source row cannot stand in for a missing verifier-owned continuation:
without the captured accept rule the assertion return does not fire. -/
theorem missing_owned_continuation_blocks_assertion_resume :
    resumedScan ∉
      cFireReflectiveSourceExecFact (resumeProgram.erase acceptRuleCapture)
        compressedAssertionResumeDirective := by
  decide +kernel

#print axioms missing_owned_continuation_blocks_assertion_resume

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeNegativeCanary
