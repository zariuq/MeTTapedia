import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The normal kernel's exact result occurrence becomes one compact proof node
at the returned stack base. -/
theorem exact_normal_result_rejoins_compact_machine :
    resultNode ∈ rejoinFinal := by
  decide +kernel

#print axioms exact_normal_result_rejoins_compact_machine

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCanary
