import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingRestoration

/-!
# The provider over apex-form obligations on every static branch

The semantic cut's own constructors ask for three different kinds of evidence
at a collapsing root: a same-colour static partner wants a plan-stop apex, a
cross-colour static partner wants restoration alignment, and a structural
partner wants leaf exposure.  The earlier split obligations asked the
collapsing arms for restoration alignment even in the same-colour branch —
strictly more than the constructor consumes.

This module restates the same-colour collapsing branch in the apex form the
constructor actually takes, mirrors the plan-stop entry point to the right
arm, and assembles the provider — hence the cost layer object and domain object —
from four obligations that match the cut constructor-for-constructor:

* `RhoAlignedPlanStops.HaveCommonRestoration` (aligned arm, apex form);
* `RhoCollapsingPlanStops.HaveCommonRestoration` (same-colour collapsing arms,
  apex form, at the forced `+ 1` measure — the endpoint pair of a collapsing
  arm is itself a retained raw stop);
* `RhoCollapsingCrossColorViewsRestorationAlignedInDomain` (cross-colour
  collapsing arms; the sort agreement facts are derived at the dispatch
  site from `sourceSort_eq_of_color_ne`, not assumed);
* `RhoCollapsingLeaf.HasExposure` (structural partners).

Nothing here retires the restoration-form obligations; both assemblies
coexist, and whichever family of obligations is discharged first seals the
object.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace RhoCanonicalStaticPairSemanticCut

/-- Right-arm mirror of `leftStaticEnclosingOfPlanStops`: the same-colour
constructor of a right-collapsing arm from raw canonical equality and the
plan-stop callback alone.  The apex keeps its left-right orientation; only
the collapsing certificate and the selected bridge constructor move. -/
noncomputable def rightStaticEnclosingOfPlanStops
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (planStops :
      RhoStaticPlanStopCommonApex leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1))) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) := by
  refine .rightStaticEnclosing rightView collapsing leftView
    (RhoMatchedStaticFramesApex.ofProvenancedRawAlignment leftView rightView
      declarationColor (rawStop :=
        RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1)) ?_ planStops)
  have nodeCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftView.node.term.1 =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightView.node.term.1 := by
    rw [leftView.patternEq, rightView.patternEq]
    exact canonical
  have below :
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 <
        sizeOf leftPattern + sizeOf rightPattern + 1 := by
    rw [leftView.patternEq, rightView.patternEq]
    exact Nat.lt_succ_self _
  exact canonicalStopAligned_of_canonicalize_eq_below _ nodeCanonical below

end RhoCanonicalStaticPairSemanticCut

/-- Right-arm mirror of the three-route reduction: the right-collapsing arm
from a same-colour plan-stop route, a cross-colour restoration route, and a
structural exposure route. -/
theorem nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_routes
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
    (canonical :
      canonicalize
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
      (leftView : left.StaticRootView leftColor), leftColor ≠ rightColor →
      RhoStaticFramesRestorationAligned leftView rightView)
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
    · exact ⟨.rightCrossColorEnclosing rightView collapsing leftView sameColor
        (crossColorRoute leftView sameColor)⟩
  · obtain ⟨exposure⟩ :=
      structuralRoute (Bool.eq_false_of_not_eq_true leftStatic)
    exact ⟨.rightEnclosing rightView collapsing exposure⟩

/-- **Obligation A2s′ — the same-colour collapsing arms in apex form.**

The measure is `+ 1` by necessity, not choice: a collapsing root is itself a
retained raw stop (`not_canonicalStopAligned_endpoints_of_collapsing`), so a
descent measured at the endpoint pair is uninhabited there.  The recursion
callback is still supplied at the endpoint measure, so it covers exactly the
proper sub-pairs; the endpoint pair itself must be handled by the apex. -/
def RhoCollapsingPlanStops.HaveCommonRestoration
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    (CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    RhoStaticPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern + 1))

/-- **The provider over apex-form obligations on every static branch.**

Each cut constructor receives exactly the evidence kind it declares: the
aligned arm a plan-stop apex at the endpoint measure, the same-colour
collapsing arms a plan-stop apex at the forced successor measure, the
cross-colour arms restoration alignment with the sort-agreement facts
derived on the spot, and the structural arms leaf exposure. -/
theorem rhoCanonicalStaticPair_hasSemanticCut_of_restorationObligations
    {declarationColor : CostStaticColor}
    (alignedApex : RhoAlignedPlanStops.HaveCommonRestoration declarationColor)
    (collapsingApex :
      RhoCollapsingPlanStops.HaveCommonRestoration declarationColor)
    (crossColor :
      RhoCollapsingCrossColorViewsRestorationAlignedInDomain declarationColor)
    (exposure : RhoCollapsingLeaf.HasExposure declarationColor) :
    RhoCanonicalStaticPair.HasSemanticCut declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape closeSmaller
    left right rootCase
  have close : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) := closeSmaller
  have closeSwapped : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf rightPattern + sizeOf leftPattern) := by
    rw [Nat.add_comm]; exact close
  cases rootCase with
  | leftCollapsing leftColor leftView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_leftCollapsing_of_routes
          leftView collapsing canonical
          (fun rightView =>
            collapsingApex leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inl collapsing) canonical)
          (fun rightView different =>
            have sortFacts :=
              CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
                leftView rightView different
            crossColor leftView rightView different sortFacts.1 sortFacts.2
              admissible leftWellSorted rightWellSorted close
              (Or.inl collapsing) canonical)
          (fun rightStructural =>
            exposure leftView admissible leftWellSorted rightWellSorted close
              collapsing rightStructural canonical)
  | rightCollapsing rightColor rightView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_routes
          rightView collapsing canonical
          (fun leftView =>
            collapsingApex leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inr collapsing) canonical)
          (fun leftView different =>
            have sortFacts :=
              CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
                leftView rightView different
            crossColor leftView rightView different sortFacts.1 sortFacts.2
              admissible leftWellSorted rightWellSorted close
              (Or.inr collapsing) canonical)
          (fun leftStructural =>
            exposure rightView admissible rightWellSorted leftWellSorted
              closeSwapped collapsing leftStructural canonical.symm)
  | aligned color leftView rightView roots =>
      exact ⟨rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex
        leftView rightView roots
        (alignedApex leftView rightView admissible leftWellSorted
          rightWellSorted close roots)⟩

/-- **The rho cost layer domain object over the restoration obligations.** -/
noncomputable def rhoHereditaryCostLayer_ofRestorationObligations
    (alignedApex : ∀ color, RhoAlignedPlanStops.HaveCommonRestoration color)
    (collapsingApex :
      ∀ color, RhoCollapsingPlanStops.HaveCommonRestoration color)
    (crossColor :
      ∀ color, RhoCollapsingCrossColorViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeaf.HasExposure color) :
    Cost.Layer :=
  rhoHereditaryCostLayer_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPair_hasSemanticCut_of_restorationObligations
        (alignedApex color) (collapsingApex color) (crossColor color)
        (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- The cost layer object laws over the restoration obligations. -/
noncomputable def rhoHereditaryCompactOpenNormalizerLaws_ofRestorationObligations
    (alignedApex : ∀ color, RhoAlignedPlanStops.HaveCommonRestoration color)
    (collapsingApex :
      ∀ color, RhoCollapsingPlanStops.HaveCommonRestoration color)
    (crossColor :
      ∀ color, RhoCollapsingCrossColorViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeaf.HasExposure color) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPair_hasSemanticCut_of_restorationObligations
        (alignedApex color) (collapsingApex color) (crossColor color)
        (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
