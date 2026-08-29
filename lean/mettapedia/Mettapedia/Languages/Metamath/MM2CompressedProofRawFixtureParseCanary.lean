import Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureParseCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

/-- The real whitespace-bearing compressed fixture parses and structurally
folds to the exact five provenance-carrying Metamath statements. -/
theorem raw_compressed_fixture_has_exact_statements :
    fixtureExactStatementsCheck = true := by
  decide +kernel

#print axioms raw_compressed_fixture_has_exact_statements

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureParseCanary
