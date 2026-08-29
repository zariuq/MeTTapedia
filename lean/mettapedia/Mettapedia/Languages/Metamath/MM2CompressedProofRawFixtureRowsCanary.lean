import Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureRowsCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

/-- Proof-neutral source admission retains `A` and `B` as two compact word
occurrences and retains the compact proof end and header cursor. -/
theorem admitted_fixture_retains_compact_rows :
    fixtureBodyA ∈ fixtureDerivedRows ∧
      fixtureBodyB ∈ fixtureDerivedRows ∧
      fixtureProofEnd ∈ fixtureDerivedRows ∧
      fixtureHeaderControl ∈ fixtureDerivedRows := by
  decide +kernel

#print axioms admitted_fixture_retains_compact_rows

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureRowsCanary
