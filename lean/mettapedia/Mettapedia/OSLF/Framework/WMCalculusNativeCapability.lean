import Mettapedia.OSLF.Framework.WMCalculusNativeAnswers

/-!
# Supported-query capabilities in native WM semantics

A specialized space need not support every query at every state. A capability
selects admissible state-query pairs and must respect WM behavioral
agreement. Its dependent answer graph is the extraction graph restricted to
those pairs. Unlike the total WM answer graph, the Sigma-image of this graph
is exactly the supported-query predicate, not necessarily top.

For a fixed query, support is also a native observation stable under
contextual WM computation. This extension adds no default evidence value for
an unsupported request and does not claim a runtime provider or query plan.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeCapability

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.GSLT.Topos

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- A state-dependent query capability that cannot distinguish states the
WM reading itself identifies observationally. -/
structure WMCapability {State Query V : Type}
    (R : WMReading State Query V) where
  supports : State → Query → Prop
  respectsAgree : ∀ first second query,
    R.Agree .state first second →
      (supports first query ↔ supports second query)

/-- Admissible requests as a native predicate over state-query pairs. -/
def supportPredicate {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Subfunctor (stateQueryObj State Query) where
  obj X := { pair | capability.supports pair.1 pair.2 }
  map := by
    intro X Y f pair supported
    exact supported

/-- The dependent answer graph restricted to admissible requests. -/
def supportedGraph {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    Subfunctor (answerTripleObj State Query V) where
  obj X := { triple |
    capability.supports triple.1.1 triple.1.2 ∧
      R.extract triple.1.1 triple.1.2 = triple.2 }
  map := by
    intro X Y f triple supported
    exact supported

/-- Restriction removes answers but never invents one outside the ordinary
WM extraction graph. -/
theorem supportedGraph_le_evidenceGraph {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    supportedGraph capability ≤ evidenceGraph R := by
  intro X triple member
  exact member.2

/-- The Sigma-image of supported answers is precisely the supported-query
predicate. No unsupported request acquires an invented default answer. -/
theorem supportedGraph_sigma_exact {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R) :
    (presheafChangeOfBase (ConstructorObj wmLanguage)).directImage
      (answerProjection State Query V) (supportedGraph capability) =
      supportPredicate capability := by
  change Subfunctor.image (supportedGraph capability)
    (answerProjection State Query V) = supportPredicate capability
  ext X pair
  constructor
  · rintro ⟨triple, supported, equal⟩
    cases equal
    exact supported.1
  · intro supported
    exact ⟨(pair, R.extract pair.1 pair.2), ⟨supported, rfl⟩, rfl⟩

/-- One unsupported request witnesses that the dependent Sigma-image is
proper, unlike the total answer graph's Sigma-image. -/
theorem supportPredicate_ne_top_of_unsupported {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (X : Opposite (ConstructorObj wmLanguage))
    (state : State) (query : Query)
    (unsupported : ¬ capability.supports state query) :
    supportPredicate capability ≠ ⊤ := by
  intro equal
  have member : (state, query) ∈ (supportPredicate capability).obj X := by
    rw [equal]
    trivial
  exact unsupported member

/-- Support for a fixed query is invariant under WM state agreement. -/
theorem supportAtQuery_invariant {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (query : Query) :
    ObservationInvariant R .state
      (fun state => capability.supports state query) := by
  intro first second agree supported
  exact (capability.respectsAgree first second query agree).1 supported

/-- Query support is a native type on authored WM programs, not merely a
set-theoretic flag beside the language. -/
def supportAtQueryNativeType {State Query V : Type}
    {R : WMReading State Query V} (capability : WMCapability R)
    (query : Query) : FullPresheafGrothendieckObj wmLanguage :=
  observationNativeType R .state
    (fun state => capability.supports state query)

/-- A contextual WM rewrite preserves a supported-query native predicate
at every generalized program and constructor stage. -/
theorem supportAtQuery_rewrite {State Query V : Type}
    {R : WMReading State Query V} (laws : R.CoreLaws)
    (capability : WMCapability R) (query : Query)
    {Γ : languagePresheafObj wmLanguage}
    {source target : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel source target) :
    (observationPredicate R .state
      (fun state => capability.supports state query)).preimage source ≤
    (observationPredicate R .state
      (fun state => capability.supports state query)).preimage target :=
  observationPredicate_rewrite R laws .state
    (fun state => capability.supports state query)
    (supportAtQuery_invariant capability query) step

end Mettapedia.OSLF.Framework.WMCalculusNativeCapability
