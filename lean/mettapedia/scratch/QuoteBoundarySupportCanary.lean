import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAvailabilityTransposition

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

example
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      plan.abstractPattern = true)
    (boundary : TypedCostRegionBoundary rhoCIGSLT color targetFree)
    (membership : boundary ∈ plan.boundaryTable.entries)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    boundary.boundary.targetSupport = [] := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have childrenFree :
          WellSorted.ReflectiveSubstitutionBinderFreeList
            children.abstractPatterns = true := by
        simpa [CostStaticRegionPlan.abstractPattern,
          WellSorted.ReflectiveSubstitutionBinderFree] using frameFree
      have childResult :=
        CostStaticArgumentPlan.boundaryTargetSupport_eq_sourceAvailable_or_nil
          children childrenFree boundary membership
      have sourceQuote : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using quoteRoot
      have quote : ReflectiveContextSupport.isQuoteConstructor
          rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true := by
        rw [sourceQuote]
        exact rho_isQuoteConstructor_quote
      rcases childResult with exposed | sealed
      · simpa [quote] using exposed
      · exact sealed
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

theorem normalizeHereditary_availabilityTransposed_eq_of_forests_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallNode.boundaryTable
        largeNode.boundaryTable smallTrees largeTrees)
    (sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1)
    (quoteRoot : smallNode.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  apply normalizeHereditary_availabilityTransposed_eq_of_forests smallNode
    largeNode smallTrees largeTrees targetBoundEq forests sourcePlanAligned
  dsimp only
  intro current smallPosition largePosition positionEq sealed nonemptySupport
  have frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      smallNode.plan.abstractPattern = true :=
    CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base smallNode.plan
      ⟨smallNode.sourceSort.1, rfl⟩
  have supportNil :=
    CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
      smallNode.plan frameFree
      (smallNode.boundaryTable.entries.get smallPosition)
      (List.get_mem _ _) quoteRoot
  exact (nonemptySupport supportNil).elim

end CostStaticRegionNode
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
