import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinNegativeCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- A formula with the wrong assertion occurrence cannot satisfy the
continuation, even when its formula and stack position are unchanged. -/
theorem wrong_assertion_occurrence_cannot_rejoin :
    resultNode ∉
      cFireReflectiveSourceExecFact wrongOccurrenceRejoinProgram
        compressedAssertionRejoinDirective := by
  decide +kernel

#print axioms wrong_assertion_occurrence_cannot_rejoin

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinNegativeCanary
