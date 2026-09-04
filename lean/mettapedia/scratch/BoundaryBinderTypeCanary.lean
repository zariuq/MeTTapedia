import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary_canary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundary : plan.rootClass.IsCertifiedBoundary) :
    ∀ domain codomain, sourceType ≠ .arrow domain codomain := by
  intro domain codomain sourceTypeEq
  cases plan with
  | boundaryApplication constructor rendered outsideCurrent certified certifies =>
      obtain ⟨category, targetTypeEq⟩ :=
        certified.exists_targetType_eq_base_of_application
      have mappedEq : mapTypeExpr (color.symbols source)
            (.arrow domain codomain) = .base category := by
        rw [← sourceTypeEq]
        exact certified.targetType_eq.symm.trans targetTypeEq
      exact TypeExpr.noConfusion mappedEq
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      rename_i collectionType elements rest
      rcases certified.targetType_collection_or_base_of_collection with
        ⟨elementType, targetTypeEq⟩ | ⟨category, targetTypeEq⟩
      · have mappedEq : mapTypeExpr (color.symbols source)
              (.arrow domain codomain) =
            .collection collectionType elementType := by
          rw [← sourceTypeEq]
          exact certified.targetType_eq.symm.trans targetTypeEq
        exact TypeExpr.noConfusion mappedEq
      · have mappedEq : mapTypeExpr (color.symbols source)
              (.arrow domain codomain) = .base category := by
          rw [← sourceTypeEq]
          exact certified.targetType_eq.symm.trans targetTypeEq
        exact TypeExpr.noConfusion mappedEq
  | bvar | fvar | application | lambda | multiLambda | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
