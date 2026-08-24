import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderObligations
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorLeafExposure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-!
# Cross-colour collapsing cuts by hereditary target rebase

A cross-colour static partner does not need to pass through the legacy raw
whole-frame restoration relation.  In a collapsing arm, production descent
selects a sealed boundary and the exact smaller-pair callback identifies its
hereditarily normalized value with the partner.  The semantic cut's enclosing
constructors consume precisely that proof-relevant leaf exposure.

The domain obligation below retains both static root views, colour inequality,
the shared non-interacting sort facts, endpoint typing, the exact recursion
callback, and canonical equality.  It is therefore distinct from the global
any-partner exposure weakening: only the cross-colour static quadrant is
rebased through this route.  The legacy raw-restoration proposition remains
available as a separate, stronger relation.
-/


open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Both oriented leaf exposures for one cross-colour static pair.  Each field
retains the collapsing certificate required to enter hereditary descent. -/
structure RhoCrossColorCollapsingLeafExposures
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor) : Prop where
  leftExposure : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern →
    Nonempty (RhoCollapsingLeafExposure leftView.node leftView.children right)
  rightExposure : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern →
    Nonempty (RhoCollapsingLeafExposure rightView.node rightView.children left)

def RhoCollapsingCrossColorViewsLeafExposuresInDomain
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor),
    leftColor ≠ rightColor →
    leftView.node.sourceSort.1 = rightView.node.sourceSort.1 →
    leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name →
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    RhoCrossColorCollapsingLeafExposures
      (declarationColor := declarationColor) leftView rightView

theorem rhoCrossColor_collapsingLeaves_haveExposure :
    ∀ declarationColor,
      RhoCollapsingCrossColorViewsLeafExposuresInDomain
        declarationColor := by
  intro declarationColor targetFree available outer leftPattern rightPattern
    type left right leftColor rightColor leftView rightView different
    sourceSortEq notInteracting admissible leftWellSorted rightWellSorted
    closeSmaller canonical
  exact
    { leftExposure := fun collapsing =>
        rhoCrossColor_leftCollapsing_leafExposure leftView rightView different
          sourceSortEq notInteracting admissible leftWellSorted rightWellSorted
          closeSmaller collapsing canonical
      rightExposure := fun collapsing =>
        rhoCrossColor_rightCollapsing_leafExposure leftView rightView different
          sourceSortEq notInteracting admissible leftWellSorted rightWellSorted
          closeSmaller collapsing canonical }

theorem nonempty_rhoCanonicalStaticPairSemanticCut_leftCollapsing_of_exposureRoutes
    {declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
    (sameColorRoute : ∀ rightView : right.StaticRootView leftColor,
      RhoStaticPlanStopCommonApex leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1)))
    (crossColorRoute : ∀ {rightColor : CostStaticColor}
      (_rightView : right.StaticRootView rightColor), leftColor ≠ rightColor →
      Nonempty (RhoCollapsingLeafExposure leftView.node leftView.children
        right))
    (structuralRoute : right.rootIsStatic = false →
      Nonempty (RhoCollapsingLeafExposure leftView.node leftView.children
        right)) :
    Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing leftColor leftView collapsing)) := by
  by_cases rightStatic : right.rootIsStatic = true
  · obtain ⟨rightColor, rightView⟩ :=
      right.staticRootView_of_rootIsStatic rightStatic
    by_cases sameColor : leftColor = rightColor
    · subst sameColor
      exact ⟨RhoCanonicalStaticPairSemanticCut.leftStaticEnclosingOfPlanStops
        leftView rightView collapsing canonical (sameColorRoute rightView)⟩
    · obtain ⟨exposure⟩ := crossColorRoute rightView sameColor
      exact ⟨.leftEnclosing leftView collapsing exposure⟩
  · obtain ⟨exposure⟩ :=
      structuralRoute (Bool.eq_false_of_not_eq_true rightStatic)
    exact ⟨.leftEnclosing leftView collapsing exposure⟩

theorem nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_exposureRoutes
    {declarationColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {rightColor : CostStaticColor}
    (rightView : right.StaticRootView rightColor)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
    (sameColorRoute : ∀ leftView : left.StaticRootView rightColor,
      RhoStaticPlanStopCommonApex leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1)))
    (crossColorRoute : ∀ {leftColor : CostStaticColor}
      (_leftView : left.StaticRootView leftColor), leftColor ≠ rightColor →
      Nonempty (RhoCollapsingLeafExposure rightView.node rightView.children
        left))
    (structuralRoute : left.rootIsStatic = false →
      Nonempty (RhoCollapsingLeafExposure rightView.node rightView.children
        left)) :
    Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing rightColor rightView collapsing)) := by
  by_cases leftStatic : left.rootIsStatic = true
  · obtain ⟨leftColor, leftView⟩ :=
      left.staticRootView_of_rootIsStatic leftStatic
    by_cases sameColor : leftColor = rightColor
    · subst sameColor
      exact ⟨RhoCanonicalStaticPairSemanticCut.rightStaticEnclosingOfPlanStops
        leftView rightView collapsing canonical (sameColorRoute leftView)⟩
    · obtain ⟨exposure⟩ := crossColorRoute leftView sameColor
      exact ⟨.rightEnclosing rightView collapsing exposure⟩
  · obtain ⟨exposure⟩ :=
      structuralRoute (Bool.eq_false_of_not_eq_true leftStatic)
    exact ⟨.rightEnclosing rightView collapsing exposure⟩

theorem rhoCanonicalStaticPair_hasSemanticCut_of_exposureA2x
    {declarationColor : CostStaticColor}
    (alignedApex : RhoAlignedPlanStops.HaveCommonRestoration declarationColor)
    (collapsingApex :
      RhoCollapsingPlanStops.HaveCommonRestoration declarationColor)
    (crossColor :
      RhoCollapsingCrossColorViewsLeafExposuresInDomain
        declarationColor)
    (exposure : RhoCollapsingLeaf.HasExposure declarationColor) :
    RhoCanonicalStaticPair.HasSemanticCut declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape closeSmaller
    left right rootCase
  have close : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) := closeSmaller
  have closeSwapped : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf rightPattern + sizeOf leftPattern) := by
    rw [Nat.add_comm]
    exact close
  cases rootCase with
  | leftCollapsing leftColor leftView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_leftCollapsing_of_exposureRoutes
          leftView collapsing canonical
          (fun rightView =>
            collapsingApex leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inl collapsing) canonical)
          (fun rightView different =>
            have sortFacts :=
              CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
                leftView rightView different
            (crossColor leftView rightView different sortFacts.1 sortFacts.2
              admissible leftWellSorted rightWellSorted close canonical
                ).leftExposure
                collapsing)
          (fun rightStructural =>
            exposure leftView admissible leftWellSorted rightWellSorted close
              collapsing rightStructural canonical)
  | rightCollapsing rightColor rightView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_exposureRoutes
          rightView collapsing canonical
          (fun leftView =>
            collapsingApex leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inr collapsing) canonical)
          (fun leftView different =>
            have sortFacts :=
              CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
                leftView rightView different
            (crossColor leftView rightView different sortFacts.1 sortFacts.2
              admissible leftWellSorted rightWellSorted close canonical
                ).rightExposure
                collapsing)
          (fun leftStructural =>
            exposure rightView admissible rightWellSorted leftWellSorted
              closeSwapped collapsing leftStructural canonical.symm)
  | aligned color leftView rightView roots =>
      exact ⟨rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex
        leftView rightView roots
        (alignedApex leftView rightView admissible leftWellSorted
          rightWellSorted close roots)⟩

/-- The rho cost layer domain object over the restoration obligations with the
cross-colour collapsing quadrant discharged by hereditary target rebase. -/
noncomputable def rhoHereditaryCostLayer_ofExposureRestorationObligations
    (alignedApex : ∀ color, RhoAlignedPlanStops.HaveCommonRestoration color)
    (collapsingApex :
      ∀ color, RhoCollapsingPlanStops.HaveCommonRestoration color)
    (crossColor : ∀ color,
      RhoCollapsingCrossColorViewsLeafExposuresInDomain color)
    (exposure : ∀ color, RhoCollapsingLeaf.HasExposure color) :
    Cost.Layer :=
  rhoHereditaryCostLayer_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPair_hasSemanticCut_of_exposureA2x
        (alignedApex color) (collapsingApex color) (crossColor color)
        (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- The rho cost layer object laws over the target-rebased cross-colour
restoration obligations. -/
noncomputable def rhoHereditaryCompactOpenNormalizerLaws_ofExposureRestorationObligations
    (alignedApex : ∀ color, RhoAlignedPlanStops.HaveCommonRestoration color)
    (collapsingApex :
      ∀ color, RhoCollapsingPlanStops.HaveCommonRestoration color)
    (crossColor : ∀ color,
      RhoCollapsingCrossColorViewsLeafExposuresInDomain color)
    (exposure : ∀ color, RhoCollapsingLeaf.HasExposure color) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPair_hasSemanticCut_of_exposureA2x
        (alignedApex color) (collapsingApex color) (crossColor color)
        (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
