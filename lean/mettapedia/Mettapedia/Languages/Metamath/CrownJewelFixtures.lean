import Mettapedia.Languages.Metamath.CrownJewelAPI
import Mettapedia.Languages.Metamath.Fixtures

/-!
# Metamath Crown-Jewel Fixture Wrappers

Small fixture-specialized wrappers over the preferred refined bridge API.
-/

namespace Mettapedia.Languages.Metamath.CrownJewelFixtures

open Mettapedia.Languages.Metamath.AcceptanceEquivalence
open Mettapedia.Languages.Metamath.CrownJewelAPI
open Mettapedia.Languages.Metamath.Fixtures
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation

/-- Preferred refined crown-jewel package specialized to the empty fixture. -/
theorem emptyBytes_preferred_crown_jewel
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored emptyBytes)
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineRefinedTraceWitness emptyBytes label f ↔ ImplAccepts emptyBytes label f) ∧
      (EngineRefinedTraceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f) ∧
      (SpecAccepts emptyBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact preferred_crown_jewel emptyBytes label f hSuccess hDisjoint

/-- Preferred refined crown-jewel package specialized to the minimal-axiom
fixture. -/
theorem minimalAxiomBytes_preferred_crown_jewel
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored minimalAxiomBytes)
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineRefinedTraceWitness minimalAxiomBytes label f ↔ ImplAccepts minimalAxiomBytes label f) ∧
      (EngineRefinedTraceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f) ∧
      (SpecAccepts minimalAxiomBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact preferred_crown_jewel minimalAxiomBytes label f hSuccess hDisjoint

end Mettapedia.Languages.Metamath.CrownJewelFixtures
