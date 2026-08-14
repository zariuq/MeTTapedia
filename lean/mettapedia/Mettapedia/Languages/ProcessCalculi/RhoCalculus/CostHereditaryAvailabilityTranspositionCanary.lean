import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesCanonicalCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryTreeAvailabilityTransposition

/-!
# Hereditary availability-transposition canaries

Moving a closed rho Cost pattern from inert outer context to active
availability can change the proof-relevant static plan.  These examples pin
the narrower property needed by matched-frame restoration: the hereditary
normalized pattern remains unchanged even when stored boundary support does
not.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostHereditaryAvailabilityTranspositionCanary

def ambientType : TypeExpr := .base (costBaseSortName "Name")

def procType : TypeExpr := .base (costBaseSortName "Proc")

def pZero : Pattern := .apply (costBaseConstructorName "PZero") []

def pDropQuoteZero : Pattern :=
  .apply (costBaseConstructorName "PDrop")
    [.apply (costBaseConstructorName "NQuote") [pZero]]

/-- A closed base process whose static region contains a nontrivial parallel
bag.  The listed order deliberately differs from structural-code order. -/
def groundBag : Pattern :=
  .apply (costBaseConstructorName "PDrop")
    [.apply (costBaseConstructorName "NQuote")
      [.collection .hashBag [pDropQuoteZero, pZero] none]]

theorem groundBagWellSortedClosed :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] procType groundBag :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [] procType groundBag).mp (by decide)

theorem groundBagWellSortedAvailable :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [ambientType] procType groundBag :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType] procType groundBag).mp (by decide)

noncomputable def groundBagSealedTree : CostRegionTree rhoCIGSLT
    FreeTypeContext.empty [] [ambientType] groundBag procType :=
  (CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := FreeTypeContext.empty) [] [ambientType] groundBag
      procType).get
    (CostRegionTree.build?_isSome_of_wellSorted groundBagWellSortedClosed)

noncomputable def groundBagClosedTree : CostRegionTree rhoCIGSLT
    FreeTypeContext.empty [] [] groundBag procType :=
  (CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := FreeTypeContext.empty) [] [] groundBag procType).get
    (CostRegionTree.build?_isSome_of_wellSorted groundBagWellSortedClosed)

noncomputable def groundBagAvailableTree : CostRegionTree rhoCIGSLT
    FreeTypeContext.empty [ambientType] [] groundBag procType :=
  (CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := FreeTypeContext.empty) [ambientType] [] groundBag
      procType).get
    (CostRegionTree.build?_isSome_of_wellSorted groundBagWellSortedAvailable)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Full-pipeline positive canary for the exact hereditary kernel: moving the
ambient Name fibre across the availability/outer split preserves the compact
normal form of a closed static region containing a parallel bag. -/
theorem groundBag_normalize_pattern_eq :
    (groundBagSealedTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
    (groundBagAvailableTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  with_unfolding_all decide

/-- The structural suffix theorem proves the load-bearing closed-to-available
step without evaluating the hereditary canonicalizer.  The separate
full-pipeline canary above also checks inert-outer transposition. -/
theorem groundBag_closed_to_available_normalize_pattern_eq :
    (groundBagClosedTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
    (groundBagAvailableTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
    (smallAvailable := []) (largeAvailable := [ambientType])
      (ambient := [ambientType]) (by simp) groundBagClosedTree
        groundBagAvailableTree rfl rfl (by decide)

/-- Negative/positive paired canary: the planner really stores different
support, so normalization invariance cannot be explained by identical plans;
nevertheless the selected boundary values normalize identically. -/
theorem boundary_support_changes_but_normal_form_does_not :
    CostHereditaryMatchedFramesCanonicalCanary.leftBoundary.boundary.targetSupport ≠
        CostHereditaryMatchedFramesCanonicalCanary.rightBoundary.boundary.targetSupport ∧
      (CostHereditaryMatchedFramesCanonicalCanary.leftChild.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (CostHereditaryMatchedFramesCanonicalCanary.rightChild.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  constructor
  · rw [CostHereditaryMatchedFramesCanonicalCanary.leftBoundary_targetSupport,
      CostHereditaryMatchedFramesCanonicalCanary.rightBoundary_targetSupport]
    simp
  · exact CostHereditaryMatchedFramesCanonicalCanary.boundary_child_normals_equal

end CostHereditaryAvailabilityTranspositionCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
