import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureActivationCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureCanary

def fixturePreparedHeaderControl :=
  deferCompressedHeaderControlRow fixtureHeaderControl

def fixtureDeferredRows :=
  deferCompressedHeaderControls fixtureDerivedRows

/-- The compact header cursor derived from the real raw source is inert until
the exact ordered theorem occurrence requests compressed verification. -/
theorem raw_fixture_header_is_prepared_not_live :
    fixturePreparedHeaderControl ∈ fixtureDeferredRows ∧
      fixtureHeaderControl ∉ fixtureDeferredRows := by
  decide +kernel

#print axioms raw_fixture_header_is_prepared_not_live

end Mettapedia.Languages.Metamath.MM2CompressedProofRawFixtureActivationCanary
