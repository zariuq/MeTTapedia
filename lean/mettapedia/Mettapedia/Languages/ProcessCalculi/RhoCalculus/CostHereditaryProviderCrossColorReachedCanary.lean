import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticDeepAtomExposure

/-!
# Cross-colour reached-case canary for the rho semantic-cut provider

A collapsing base Quote/Drop chain can reach another base sub-plan whose
terminal payload is a wrapped static application in the shared Name fibre.
Consequently the provider's cross-colour reached branch is inhabited and
cannot be eliminated by an impossibility lemma.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

namespace CostHereditaryProviderCrossColorReachedCanary

/-- Declaration used by the base-colour provider. -/
def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

/-- Wrapped static endpoint, rigid under the base declaration. -/
def rightPattern : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []]

/-- Inner base collapse whose terminal is the wrapped endpoint. -/
def reachedPattern : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [rightPattern]]

/-- A second base collapse around the reached inner plan. -/
def leftPattern : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [reachedPattern]]

private theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] (.base (costBaseSortName "Name"))
      rightPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected _membership
  simp [rightPattern, binderSafeAt, binderSafeListAt]

private theorem rightBoundaryCertificate_exists :
    ∃ certificate,
      certifyCostRegionBoundary? rhoCIGSLT .base FreeTypeContext.empty []
          (.base (costBaseSortName "Name")) rightPattern =
        some certificate := by
  apply exists_certifyCostRegionBoundary?_eq_some
  · exact ⟨.base "Name", by rfl⟩
  · exact rightWellSorted

noncomputable def rightBoundaryCertificate :
    CertifiedCostRegionBoundary rhoCIGSLT .base FreeTypeContext.empty []
      (.base (costBaseSortName "Name")) rightPattern :=
  Classical.choose rightBoundaryCertificate_exists

theorem rightBoundaryCertificate_spec :
    certifyCostRegionBoundary? rhoCIGSLT .base FreeTypeContext.empty []
        (.base (costBaseSortName "Name")) rightPattern =
      some rightBoundaryCertificate :=
  Classical.choose_spec rightBoundaryCertificate_exists

private theorem rule_mem (index : Nat) (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

private def wrappedQuoteConstructor :
    DeclaredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[2], rule_mem 2 (by omega)⟩

private theorem wrappedQuote_selected :
    wrappedQuoteConstructor ∈
      rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    wrappedQuoteConstructor).2
  constructor <;> decide

private def wrappedQuoteDeclared : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped wrappedQuoteConstructor, wrappedQuote_selected⟩

private theorem wrappedQuoteRole :
    rhoCIGSLT.declaredCostConstructorRole wrappedQuoteDeclared =
      .static .wrapped := rfl

private theorem wrappedQuoteOutsideBase :
    rhoCIGSLT.declaredCostConstructorRole wrappedQuoteDeclared ≠
      .static .base := by
  rw [wrappedQuoteRole]
  decide

private noncomputable def rightBoundaryPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer rightPattern (.base "Name") :=
  .boundaryApplication wrappedQuoteDeclared rfl wrappedQuoteOutsideBase
    rightBoundaryCertificate rightBoundaryCertificate_spec

private noncomputable def reachedDropPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer
      (.apply (costBaseConstructorName "PDrop") [rightPattern])
      (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseDropDeclared rfl
    rhoBreadthBaseDropRole rhoBreadthBaseDropPreimage
  · exact rhoBreadthBaseDrop_notBare
  · exact .cons (by trivial) rfl
      (rightBoundaryPlan
        (outer.comp
          (.apply (costBaseConstructorName "PDrop") [] .hole [])))
      .nil

private noncomputable def reachedPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer reachedPattern (.base "Name") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseQuoteDeclared rfl
    rhoBreadthBaseQuoteRole rhoBreadthBaseQuotePreimage
  · exact rhoBreadthBaseQuote_notBare
  · exact .cons (by trivial) rfl
      (reachedDropPlan
        (outer.comp
          (.apply (costBaseConstructorName "NQuote") [] .hole [])))
      .nil

private noncomputable def outerDropPlan (outer : OneHoleContext) :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] outer
      (.apply (costBaseConstructorName "PDrop") [reachedPattern])
      (.base "Proc") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseDropDeclared rfl
    rhoBreadthBaseDropRole rhoBreadthBaseDropPreimage
  · exact rhoBreadthBaseDrop_notBare
  · exact .cons (by trivial) rfl
      (reachedPlan
        (outer.comp
          (.apply (costBaseConstructorName "PDrop") [] .hole [])))
      .nil

/-- The genuine base-colour static plan for the two-shell endpoint. -/
noncomputable def leftPlan :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base []) []
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole leftPattern (.base "Name") := by
  apply CostStaticRegionPlan.application rhoBreadthBaseQuoteDeclared rfl
    rhoBreadthBaseQuoteRole rhoBreadthBaseQuotePreimage
  · exact rhoBreadthBaseQuote_notBare
  · exact .cons (by trivial) rfl
      (outerDropPlan
        (OneHoleContext.hole.comp
          (.apply (costBaseConstructorName "NQuote") [] .hole [])))
      .nil

/-- Traversal through the outer Quote/Drop shell genuinely reaches the inner
base plan; it does not stop at the wrapped terminal boundary. -/
noncomputable def leftReached :
    CostStaticPlanReached rhoCIGSLT .base FreeTypeContext.empty
      reachedPattern leftPlan.abstractPattern where
  sourceBound := _
  targetBound := []
  thinning := _
  sourceAvailable := []
  outer :=
    (OneHoleContext.hole.comp
      (.apply (costBaseConstructorName "NQuote") [] .hole [])).comp
        (.apply (costBaseConstructorName "PDrop") [] .hole [])
  sourceType := .base "Name"
  plan := reachedPlan _
  skeletonContext :=
    .apply "NQuote" [] (.apply "PDrop" [] .hole []) []
  abstract_eq := by
    unfold leftPlan outerDropPlan
    simp only [CostStaticRegionPlan.abstractPattern,
      CostStaticArgumentPlan.abstractPatterns, OneHoleContext.fill,
      rhoBreadthBaseQuotePreimage, rhoBreadthBaseDropPreimage,
      costStaticConstructorPreimage, rhoBreadthBaseQuoteDeclared,
      rhoBreadthBaseDropDeclared, rhoCalc, List.nil_append]
    rfl

/-- The wrapped endpoint has an intrinsic wrapped static root. -/
def rightStaticShape :
    CostStaticRootShape rhoCIGSLT rightPattern
      (.base (costBaseSortName "Name")) := by
  apply CostStaticRootShape.application .wrapped wrappedQuoteDeclared
  · simpa [rightPattern, wrappedQuoteDeclared, wrappedQuoteConstructor,
      CIGSLT.renderDeclaredCostConstructor,
      CIGSLT.renderGeneratedCostConstructor, CostConstructor.render, rhoCalc] using
      rhoCIGSLT.decodeDeclaredCostConstructor_render wrappedQuoteDeclared
  · exact wrappedQuoteRole

/-- Exact proposition asserted by the discarded fixed-colour vacuity route. -/
def CrossColorReachedVacuous : Prop :=
  canonicalize declaration leftPattern = canonicalize declaration rightPattern →
    CollapsingRoot declaration leftPattern →
    CostStaticRootShape rhoCIGSLT rightPattern
      (.base (costBaseSortName "Name")) →
    Nonempty (CostStaticPlanReached rhoCIGSLT .base FreeTypeContext.empty
      reachedPattern leftPlan.abstractPattern) →
    False

/-- The provider's cross-colour reached branch is inhabited. -/
theorem crossColorReachedVacuous_false : ¬ CrossColorReachedVacuous := by
  intro vacuous
  exact vacuous (by decide) (Or.inl ⟨_, rfl⟩) rightStaticShape
    ⟨leftReached⟩

/-- Positive control: peeling one shell supplies the strict recursive decrease
needed by the provider. -/
theorem reachedPair_size_decreases :
    sizeOf reachedPattern + sizeOf rightPattern <
      sizeOf leftPattern + sizeOf rightPattern := by
  have : sizeOf reachedPattern < sizeOf leftPattern := by decide
  omega

/-- Following the reached inner plan to its wrapped terminal produces one
exact stopped boundary beneath two Quote/Drop shells. -/
noncomputable def terminalStopped :
    CostStaticPlanStopped rhoCIGSLT .base FreeTypeContext.empty rightPattern
      leftPlan.abstractPattern where
  boundarySupport := []
  boundaryType := .base (costBaseSortName "Name")
  content := rightPattern
  certified := rightBoundaryCertificate
  certifies := rightBoundaryCertificate_spec
  residual := .hole
  content_eq := rfl
  skeletonContext :=
    .apply "NQuote" []
      (.apply "PDrop" []
        (.apply "NQuote" []
          (.apply "PDrop" [] .hole []) []) []) []
  abstract_eq := by
    unfold leftPlan outerDropPlan reachedPlan reachedDropPlan rightBoundaryPlan
    simp only [CostStaticRegionPlan.abstractPattern,
      CostStaticArgumentPlan.abstractPatterns, OneHoleContext.fill,
      rhoBreadthBaseQuotePreimage, rhoBreadthBaseDropPreimage,
      costStaticConstructorPreimage, rhoBreadthBaseQuoteDeclared,
      rhoBreadthBaseDropDeclared, rhoCalc, List.nil_append]
    rfl

/-- Positive control for the replacement route: the exact terminal context
is accepted as a depth-two atom shell. -/
theorem terminalStopped_atomShell :
    RhoCanonicalAtomShell terminalStopped.skeletonContext :=
  .quoteDrop (.quoteDrop .hole)

end CostHereditaryProviderCrossColorReachedCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
