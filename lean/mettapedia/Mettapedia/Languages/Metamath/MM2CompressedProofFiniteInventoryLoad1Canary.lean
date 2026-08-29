import Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad0Canary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad1Canary

open Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The second concrete loader step consumes the state produced by occurrence
zero and transports the second opaque rule exactly. -/
theorem load_occurrence_one_exact :
    cReflectiveSourceWorkQueueStep .leaveInert afterLoad0 =
      some afterLoad1 := by
  rfl

#print axioms load_occurrence_one_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad1Canary
