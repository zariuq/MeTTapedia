import Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad0Canary

open Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- The first concrete loader step has the exact state declared by the
two-occurrence presentation. -/
theorem load_occurrence_zero_exact :
    cReflectiveSourceWorkQueueStep .leaveInert twoRuleProgram =
      some afterLoad0 := by
  rfl

#print axioms load_occurrence_zero_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryLoad0Canary
