import Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureNeutralCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

/-- Source admission emits compact syntax and allocation data, but never a
decoded proof step, a verified heap proof, or an acceptance verdict. -/
theorem admitted_fixture_does_not_perform_proof_work :
    fixtureDerivedRows.any (atomHasHead "mm-compressed-step-pending") = false ∧
      fixtureDerivedRows.any (atomHasHead "mm-compressed-heap-proof") = false ∧
      fixtureDerivedRows.any (atomHasHead "mm-accepted") = false := by
  decide +kernel

#print axioms admitted_fixture_does_not_perform_proof_work

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureNeutralCanary
