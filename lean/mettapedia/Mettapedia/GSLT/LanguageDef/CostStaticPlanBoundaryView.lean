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
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
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

/-- Outside the certified-boundary/boundary quadrant, structural stop
eligibility has exactly four shapes: paired Quote, either orientation of a
foreign/source collection, or paired bare parallel.  In particular, rigid
leaves and ordinary applications cannot enter the semantic stop callback. -/
theorem CostStaticPlanStopEligible.nonBoundary_cases
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (declaration : ReflectivePresentationDecl)
    (leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType)
    (eligible : CostStaticPlanStopEligible declaration leftPlan rightPlan)
    (notBoth :
      ¬ (leftPlan.rootClass.IsCertifiedBoundary ∧
        rightPlan.rootClass.IsCertifiedBoundary)) :
    (leftPlan.rootClass = .application declaration.quoteConstructor ∧
      rightPlan.rootClass = .application declaration.quoteConstructor) ∨
    (leftPlan.rootClass = .boundaryCollection ∧
      ∃ collectionType, rightPlan.rootClass = .collection collectionType) ∨
    ((∃ collectionType, leftPlan.rootClass = .collection collectionType) ∧
      rightPlan.rootClass = .boundaryCollection) ∨
    (leftPlan.rootClass = .collection declaration.parallelCollection ∧
      rightPlan.rootClass = .collection declaration.parallelCollection) := by
  cases hLeft : leftPlan.rootClass <;>
    cases hRight : rightPlan.rootClass <;>
    simp [CostStaticPlanStopEligible, hLeft, hRight,
      CostStaticPlanRootClass.IsCertifiedBoundary] at eligible notBoth ⊢
  all_goals exact eligible

/-- Once paired Quote and every certified-boundary side have been removed,
the only remaining structurally eligible stop is paired bare parallel. -/
theorem CostStaticPlanStopEligible.parallel_of_nonBoundary_residual
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPattern rightPattern : Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    {leftPlan : CostStaticRegionPlan source color targetFree leftSourceBound
      leftTargetBound leftThinning leftAvailable leftOuter leftPattern
      leftSourceType}
    {rightPlan : CostStaticRegionPlan source color targetFree rightSourceBound
      rightTargetBound rightThinning rightAvailable rightOuter rightPattern
      rightSourceType}
    {declaration : ReflectivePresentationDecl}
    (eligible : CostStaticPlanStopEligible declaration leftPlan rightPlan)
    (notBoth : ¬ (leftPlan.rootClass.IsCertifiedBoundary ∧
      rightPlan.rootClass.IsCertifiedBoundary))
    (notQuote : ¬ (leftPlan.rootClass =
        .application declaration.quoteConstructor ∧
      rightPlan.rootClass = .application declaration.quoteConstructor))
    (neitherBoundary : ¬ leftPlan.rootClass.IsCertifiedBoundary ∧
      ¬ rightPlan.rootClass.IsCertifiedBoundary) :
    leftPlan.rootClass = .collection declaration.parallelCollection ∧
      rightPlan.rootClass = .collection declaration.parallelCollection := by
  rcases CostStaticPlanStopEligible.nonBoundary_cases declaration leftPlan
      rightPlan eligible notBoth with quote | mixedLeft | mixedRight | parallel
  · exact (notQuote quote).elim
  · exact (neitherBoundary.1 (Or.inr mixedLeft.1)).elim
  · exact (neitherBoundary.2 (Or.inr mixedRight.2)).elim
  · exact parallel

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

/-- A reached certified boundary is strictly smaller than its enclosing static
root.  Consequently, pairing it with any payload bounded by the other root is
strictly smaller than the enclosing root pair. -/
theorem mixed_pair_size_lt_of_left_boundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftPayload rightPayload leftAbstract : Pattern}
    (leftReached : CostStaticPlanReached source color targetFree leftPayload
      leftAbstract)
    (leftBoundary : leftReached.BoundaryView)
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightBound : sizeOf rightPayload ≤ sizeOf rightNode.term.1) :
    sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries :=
    leftEmbedding.subset (by
      rw [leftBoundary.entries_eq]
      simp)
  have leftStrict :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot
      leftNode.rootStatic leftBoundary.stopped.certified.typed leftMember
  rw [leftBoundary.content_eq] at leftStrict
  omega

/-- Symmetric strictness when the right reached plan is a certified boundary. -/
theorem mixed_pair_size_lt_of_right_boundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftPayload rightPayload rightAbstract : Pattern}
    (rightReached : CostStaticPlanReached source color targetFree rightPayload
      rightAbstract)
    (rightBoundary : rightReached.BoundaryView)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (leftBound : sizeOf leftPayload ≤ sizeOf leftNode.term.1) :
    sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
  have rightMember : rightBoundary.stopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries :=
    rightEmbedding.subset (by
      rw [rightBoundary.entries_eq]
      simp)
  have rightStrict :=
    rightNode.plan.boundary_content_size_lt_of_isStaticRoot
      rightNode.rootStatic rightBoundary.stopped.certified.typed rightMember
  rw [rightBoundary.content_eq] at rightStrict
  omega

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
