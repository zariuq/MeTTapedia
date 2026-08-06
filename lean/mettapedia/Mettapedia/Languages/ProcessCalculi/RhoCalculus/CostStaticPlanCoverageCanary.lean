import Mettapedia.GSLT.LanguageDef.CostStaticPlanOccurrenceCoverage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageClosureFixture

/-!
# Occurrence-tied coverage canaries: the breadth witness through the
generic route

The two-sibling breadth occurrence is reconstructed through the generic
coverage machinery: a typed occurrence with its retained authored origin,
one covered cell per changed sibling — each localized by an explicit
context and tied to the occurrence's source declaration — and the generic
assembly reproducing the hand-built hereditary tree alignment and the exact
executor collapse.  The name cell closes at a skeleton-level semantic atom;
the continuation cell closes at the restoration apex, exactly as the
respelling falsifier demands.  Negative canaries show that no coverage of
this occurrence can be cell-free and that an equation-shaped cell edge can
never tie to the reflective occurrence.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- The complete per-site classification of the breadth spine: both changed
siblings covered, no untouched sibling misclassified. -/
noncomputable def rhoBreadthSiteClassification :
    CostArgumentSiteClassification rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthTypedOccurrence.sourceDeclaration
      rhoBreadthLeftSpine rhoBreadthRightSpine :=
  .changed (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
    (by rw [rhoBreadthOutputFirstParam]; exact True.intro)
    (by rw [rhoBreadthOutputFirstParam]; rfl)
    rhoCutOrderBaseRedexTree rhoCutOrderZeroStructuralTree
    rhoCoverageNameSiteClosure
    (.changed (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
      (by rw [rhoBreadthOutputSecondParam]; exact True.intro)
      (by rw [rhoBreadthOutputSecondParam]; rfl)
      rhoBreadthLeftProcessTree rhoBreadthRightProcessTree
      rhoCoverageContinuationSiteClosure
      .nil)

/-- The breadth witness through the generic covered family. -/
noncomputable def rhoBreadthCoverage :
    CostOccurrenceTiedSpineCoverage rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoBreadth_generator
      rhoBreadthTypedOccurrence where
  rule := rhoBreadthOutputRule
  membership := rhoBreadthOutputMembership
  notBareCollection := rhoBreadthOutput_notBare
  constructor := rhoBreadthOutputDeclared
  materializes := rhoBreadthOutput_materializes
  neutral := Or.inl rhoBreadthOutputRole
  ordinary := rhoBreadthOutput_notQuote
  category_eq := rfl
  leftArguments := [rhoCutOrderRedex, rhoBreadthLeftProcess]
  rightArguments := [.fvar "0", rhoBreadthRightProcess]
  leftPattern_eq := rfl
  rightPattern_eq := rfl
  leftSpine := rhoBreadthLeftSpine
  rightSpine := rhoBreadthRightSpine
  sites := rhoBreadthSiteClassification

/-! ## Positive coverage canaries -/

/-- The localization retained by the continuation witness really exposes one
semantic leaf inside a shared structural context.  Fixed free variables are
reflexive; only the selected cell is allowed to change. -/
theorem rhoCoverageContinuationSite_patternLeafAligned :
    PatternLeafAligned
      (fun left right =>
        left = right ∨
          (left = rhoCoverageContinuationSiteWitness.cell.first.pattern ∧
            right = rhoCoverageContinuationSiteWitness.cell.second.pattern))
      rhoBreadthLeftProcess rhoBreadthRightProcess :=
  rhoCoverageContinuationSiteWitness.patternLeafAlignedWithContext
    (.apply (costWrappedConstructorName "PDrop") [] [] .nil .hole .nil)
    (Or.inr ⟨rfl, rfl⟩)

/-- The breadth occurrence yields exactly two covered changed cells. -/
theorem rhoBreadthCoverage_two_cells :
    rhoBreadthCoverage.sites.changedCount = 2 := rfl

/-- The generic assembly reproduces the hand-built hereditary alignment
result for the two-sibling witness. -/
theorem rhoBreadthCoverage_normalize_eq :
    (rhoBreadthCoverage.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthCoverage.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  simpa [rhoHereditaryNormalizationKernel] using
    rhoBreadthCoverage.toTreeAlignment.normalize_pattern_eq

/-- The generic covered family assembles into the full generator alignment
and re-derives the exact hereditary executor collapse of the breadth
edge. -/
theorem rhoBreadth_executor_eq_viaCoverage :
    rhoCostNormalizeOpenHereditary rhoBreadthLeft =
      rhoCostNormalizeOpenHereditary rhoBreadthRight := by
  apply Subtype.ext
  have span := rhoBreadthCoverage.toGeneratorAlignment.toNormalizationLift.span
  exact span.compiledPatterns_eq rhoHereditaryCompactCoherent

/-! ## Negative coverage canaries -/

/-- No covered family for the breadth occurrence can be cell-free: the two
endpoint terms differ, so coverage forces at least one changed cell.  The
raw candidate carrier's empty family is therefore not coverage. -/
theorem rhoBreadth_coverage_never_empty
    (coverage : CostOccurrenceTiedSpineCoverage rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoBreadth_generator
      rhoBreadthTypedOccurrence) :
    0 < coverage.sites.changedCount :=
  coverage.changedCount_pos_of_endpoints_ne (by
    intro absurd
    rw [show rhoBreadthLeft.1 = rhoBreadthLeftPattern from rfl,
      show rhoBreadthRight.1 = rhoBreadthRightPattern from rfl] at absurd
    simp [rhoBreadthLeftPattern, rhoBreadthRightPattern, rhoCutOrderRedex,
      rhoCutOrderBaseQuote, rhoCutOrderBaseDrop] at absurd)

/-- An equation-shaped cell edge can never be tied to the reflective breadth
occurrence: the declaration tie separates the two authored generator
families. -/
theorem rhoCoverage_unrelatedEdge_rejected
    (cell : CostStaticPlanSiblingPairCell rhoCIGSLT rhoCutOrderFree)
    (isEquation : ∃ used,
      cell.sourceDeclaration = .equation used) :
    cell.sourceDeclaration ≠
      rhoBreadthTypedOccurrence.sourceDeclaration := by
  obtain ⟨used, isEquation⟩ := isEquation
  rw [isEquation, rhoBreadthTypedOccurrence_sourceDeclaration]
  intro impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
