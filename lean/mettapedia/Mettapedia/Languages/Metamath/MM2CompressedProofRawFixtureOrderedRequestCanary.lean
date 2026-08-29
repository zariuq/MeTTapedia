import Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureActivationCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureOrderedRequestCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureActivationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def fixtureTheoremStatement : RawStatement :=
  fixtureStatements[4]'(by decide)

def fixtureTheoremRequest : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", fixtureOwner, natAtom 4,
      natAtom 5, rawStatementAtom fixtureTheoremStatement]

def fixtureInitialLoading : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", fixtureOwner, natAtom 4,
      fixtureProofOwner, fixtureHeaderControl, natAtom 0]

def fixtureActivationProgram : List Atom :=
  sourceCompressedProofActivateRule :: fixtureTheoremRequest ::
    fixtureDeferredRows

def fixtureActivationFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1
    fixtureActivationProgram).1

/-- The exact theorem occurrence parsed from the raw fixture activates its
own compact proof rows and starts verifier-inventory loading at position zero. -/
theorem raw_fixture_exact_request_starts_inventory_loading :
    fixtureInitialLoading ∈ fixtureActivationFinal ∧
      fixtureTheoremRequest ∉ fixtureActivationFinal ∧
      fixturePreparedHeaderControl ∉ fixtureActivationFinal := by
  decide +kernel

#print axioms raw_fixture_exact_request_starts_inventory_loading

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureOrderedRequestCanary
