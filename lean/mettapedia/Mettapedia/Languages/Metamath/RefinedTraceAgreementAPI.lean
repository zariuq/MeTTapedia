import Mettapedia.Languages.Metamath.AcceptanceEquivalence

/-!
# Metamath Refined-Trace Agreement API

This module keeps the strongest currently available bridge theorem easy to
consume from downstream code.
-/

namespace Mettapedia.Languages.Metamath.RefinedTraceAgreementAPI

open Mettapedia.Languages.Metamath.AcceptanceEquivalence
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation

/-- Preferred public bridge theorem.

Positive example:
- use this theorem when runtime-provenance disjointness is available and you
  want refined runtime-to-engine trace evidence.

Negative example:
- do not default to the weak witness layer when refined evidence is required
  by downstream theorem obligations.
-/
theorem preferred_refinedTraceAgreement
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes) :
    (EngineRefinedTraceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineRefinedTraceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  exact metamath_languageDef_refinedTraceAgreement_of_runtimeProvenanceDisjoint
    bytes label f hSuccess hDisjoint

/-- Extraction corollary: preferred refined-trace agreement gives declarative engine-path
existence from spec acceptance. -/
theorem preferred_refinedTraceAgreement_enginePath
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  exact (preferred_refinedTraceAgreement bytes label f hSuccess hDisjoint).2.2 hSpec

/-- Compatibility corollary: the weak bridge is still available, but this
theorem makes the preferred refined route explicit in call sites. -/
theorem weak_bridge_via_preferred
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes) :
    (EngineAcceptanceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  exact metamath_languageDef_bridge_of_runtimeProvenanceDisjoint
    bytes label f hSuccess hDisjoint

end Mettapedia.Languages.Metamath.RefinedTraceAgreementAPI
