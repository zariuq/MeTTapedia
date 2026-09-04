import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Descent lemma, stated at the plan of the left static root view. -/
theorem descent
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    {target : Pattern}
    (canonical :
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) pattern = target)
    (escape :
      (∃ wire arguments, target = .apply wire arguments ∧
          decodeCostStaticConstructor color wire = none) ∨
      (∃ collectionType elements rest, target = .collection collectionType elements rest ∧
          collectionType ≠
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl).parallelCollection)) :
    ∃ payload, Nonempty
      { state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
          plan.abstractPattern //
        canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
            (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
              .fvar state.boundaryOccurrence.name
        ∧ Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
            [state.certified.typed] plan.boundaryTable.entries)
        ∧ canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            state.certified.typed.boundary.content = target
        ∧ state.certified.typed.boundary.targetSupport = sourceAvailable
        ∧ state.certified.typed.boundary.targetType =
            mapTypeExpr (color.symbols rhoCIGSLT) sourceType } := by
  sorry

theorem probeCrossLeft
    {declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern)) :
    Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing leftColor leftView collapsing)) := by
  -- the declaration colour is the collapsing side's colour
  have colorEq : declarationColor = leftColor := by sorry
  subst colorEq
  obtain ⟨payload, ⟨state, contextCollapse, ⟨entryEmbedding⟩, boundaryCanonical,
      boundarySupport, boundaryType⟩⟩ :=
    descent (color := declarationColor) leftView.node.plan
      (target := canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) rightPattern)
      (by rw [← canonical, leftView.patternEq]) (by sorry)
  refine ⟨.leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedCollapseOfCloseSmaller
      (declarationColor := declarationColor)
      left right leftView rightWellSorted
      (state := by rw [← leftView.node.skeleton_pattern] at *; exact state)
      ?entryEmbedding ?contextCollapse ?boundaryCanonical ?boundarySupport
      ?boundaryType closeSmaller)⟩
  all_goals sorry
