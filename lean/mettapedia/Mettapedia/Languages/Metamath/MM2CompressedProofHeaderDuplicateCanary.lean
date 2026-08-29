import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderDuplicateCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Duplicate detection has strictly earlier scheduler priority than the
ordinary explicit-hypothesis loader and therefore cannot allocate a second
copy of a mandatory hypothesis. -/
theorem duplicate_mandatory_label_faults_before_explicit_load :
    let final :=
      (cReflectiveSourceWorkQueueRunN .leaveInert 1 duplicateProgram).1
    duplicateFault ∈ final ∧ mandatoryHeap ∉ final := by
  decide +kernel

#print axioms duplicate_mandatory_label_faults_before_explicit_load

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderDuplicateCanary
