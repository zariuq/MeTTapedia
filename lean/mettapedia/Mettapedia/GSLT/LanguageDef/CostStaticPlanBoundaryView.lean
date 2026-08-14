import Mettapedia.GSLT.LanguageDef.CostStaticPlanCanonicalAlignment

/-!
# Certified boundary views of reached Cost plans

A reached plan classified as a foreign application or collection contains one
certified boundary entry.  This module exposes that entry through the generic
`CostStaticPlanReached.BoundaryView`, retaining all equalities needed by
semantic consumers without making the two boundary syntaxes share a fake
constructor.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- The two reached-plan root classes that carry one certified foreign
boundary as their complete local table. -/
def CostStaticPlanRootClass.IsCertifiedBoundary
    (rootClass : CostStaticPlanRootClass) : Prop :=
  rootClass = .boundaryApplication ∨ rootClass = .boundaryCollection

/-- Rigid source roots do not claim a certified foreign-boundary view. -/
theorem not_rigid_isCertifiedBoundary :
    ¬ CostStaticPlanRootClass.rigid.IsCertifiedBoundary := by
  simp [CostStaticPlanRootClass.IsCertifiedBoundary]

namespace CostStaticPlanReached

/-- A reached plan whose root class is a certified boundary exposes an exact
singleton boundary view. -/
theorem nonempty_boundaryView_of_boundaryClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached source color targetFree payload rootAbstract)
    (boundaryClass : state.plan.rootClass.IsCertifiedBoundary) :
    Nonempty state.BoundaryView := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan with
  | @boundaryApplication _ _ _ _ _ wireName arguments sourceType constructor
      rendered outsideCurrent certified certifies =>
      let stopped : CostStaticPlanStopped source color targetFree
          (.apply wireName arguments)
          rootAbstract :=
        { boundarySupport := sourceAvailable
          boundaryType := mapTypeExpr (color.symbols source) sourceType
          content := .apply wireName arguments
          certified := certified
          certifies := certifies
          residual := .hole
          content_eq := rfl
          skeletonContext := skeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using abstractEq }
      exact ⟨
        { stopped := stopped
          entries_eq := rfl
          targetSupport_eq := certified.targetSupport_eq
          targetType_eq := certified.targetType_eq
          content_eq := certified.content_eq
          abstract_eq := rfl }⟩
  | @boundaryCollection _ _ _ _ _ collectionType elements rest sourceType
      currentRejected oppositeChoice oppositeSelected certified certifies =>
      let stopped : CostStaticPlanStopped source color targetFree
          (.collection collectionType elements rest)
          rootAbstract :=
        { boundarySupport := sourceAvailable
          boundaryType := mapTypeExpr (color.symbols source) sourceType
          content := .collection collectionType elements rest
          certified := certified
          certifies := certifies
          residual := .hole
          content_eq := rfl
          skeletonContext := skeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using abstractEq }
      exact ⟨
        { stopped := stopped
          entries_eq := rfl
          targetSupport_eq := certified.targetSupport_eq
          targetType_eq := certified.targetType_eq
          content_eq := certified.content_eq
          abstract_eq := rfl }⟩
  | bvar | fvar | application | lambda | multiLambda | collection =>
      simp [CostStaticPlanRootClass.IsCertifiedBoundary,
        CostStaticRegionPlan.rootClass] at boundaryClass

/-- Positive control: an explicitly retained boundary view remembers exactly
one local table entry. -/
theorem BoundaryView.entries_singleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    {state : CostStaticPlanReached source color targetFree payload rootAbstract}
    (view : state.BoundaryView) :
    state.plan.boundaryTable.entries.length = 1 := by
  rw [view.entries_eq]
  rfl

/-- Negative control: a reached plan with an empty boundary table cannot have
a certified boundary view. -/
theorem not_boundaryView_of_entries_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    {state : CostStaticPlanReached source color targetFree payload rootAbstract}
    (entriesNil : state.plan.boundaryTable.entries = []) :
    ¬ Nonempty state.BoundaryView := by
  rintro ⟨view⟩
  have singleton := view.entries_singleton
  rw [entriesNil] at singleton
  simp at singleton

end CostStaticPlanReached

end Mettapedia.GSLT.LanguageDef
