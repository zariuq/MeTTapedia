import Mettapedia.Languages.Metamath.RefinedTraceAgreementAPI
import Mettapedia.Languages.Metamath.Fixtures

/-!
# Metamath Refined-Trace Agreement Fixtures

Small fixture-specialized wrappers over the preferred refined bridge API.
-/

namespace Mettapedia.Languages.Metamath.RefinedTraceAgreementFixtures

open Mettapedia.Languages.Metamath.AcceptanceEquivalence
open Mettapedia.Languages.Metamath.RefinedTraceAgreementAPI
open Mettapedia.Languages.Metamath.Fixtures
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation

/-- Preferred refined-trace agreement specialized to the empty fixture. -/
theorem emptyBytes_preferred_refinedTraceAgreement
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored emptyBytes)
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineRefinedTraceWitness emptyBytes label f ↔ ImplAccepts emptyBytes label f) ∧
      (EngineRefinedTraceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f) ∧
      (SpecAccepts emptyBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact preferred_refinedTraceAgreement emptyBytes label f hSuccess hDisjoint

/-- Preferred refined-trace agreement specialized to the minimal-axiom
fixture. -/
theorem minimalAxiomBytes_preferred_refinedTraceAgreement
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored minimalAxiomBytes)
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineRefinedTraceWitness minimalAxiomBytes label f ↔ ImplAccepts minimalAxiomBytes label f) ∧
      (EngineRefinedTraceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f) ∧
      (SpecAccepts minimalAxiomBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact preferred_refinedTraceAgreement minimalAxiomBytes label f hSuccess hDisjoint

end Mettapedia.Languages.Metamath.RefinedTraceAgreementFixtures
