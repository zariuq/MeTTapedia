import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderApexSlice
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryResidualSwitchboard

/-!
# What the proof-relevant recursive step buys the apex slice

`RhoCanonicalPairRecursiveResult.nonempty_of_step` closes the proof-relevant
paired recursion from `RhoCanonicalPairRecursiveStep` by the symmetric size
measure.  The closure is *measure-free at the point of use*: it produces a
result for every admissible, well-sorted, canonically equal pair, not only for
pairs strictly below some parent budget.  That is what this module exploits.

Two consequences are recorded here.

* `rhoStaticPlanStopCommonApex_sameColor_of_recursiveStep` — at views of the
  declaration's own colour, the step discharges the plan-stop apex obligation
  at *every* raw stop whose stops carry canonical equality.  No size budget is
  consumed, so the endpoint measure and the successor measure are alike.
* The two apex-slice obligations then reduce to their foreign-colour halves
  alone (`rhoAlignedViewsPlanStopApexInDomain_of_recursiveStep`,
  `rhoCollapsingViewsPlanStopApexInDomain_of_recursiveStep`).

The colour restriction is not an artifact of the proof.
`RhoCanonicalPairRecursiveResult.reachedApex` is a
`RhoReachedPlanPairApexAction` at the *declaration's* colour, and that action
quantifies over `left.StaticRootView declarationColor`.  A pair of views
coloured `color ≠ declarationColor` cannot instantiate it at all: only the
compact `pair` field survives there.  So the step says nothing about the
foreign-colour half of either obligation, which is retained as an explicit
hypothesis in both reductions below.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## The endpoint-measure gate, in both directions

`not_canonicalStopAligned_endpoints_of_collapsing` records that a collapsing
endpoint has no raw descent measured at itself.  The converse is recorded here,
so the gate becomes an equivalence: at the endpoint measure the raw descent
exists exactly when neither endpoint collapses.  That is the whole reason
`RhoCollapsingViewsPlanStopApexInDomain` is stated one above the endpoint pair
while `RhoAlignedViewsPlanStopApexInDomain` is stated at it. -/

/-- **A non-collapsing canonical pair does descend at its own measure.**

The root dichotomy leaves a `CanonicalRootAligned` once both collapsing cases
are excluded, and `canonicalStopAligned_of_root_aligned` forces exactly one
rigid step before delegating, so every retained stop lies strictly below the
endpoint pair. -/
theorem rhoCanonicalStopAligned_endpoints_of_not_collapsing
    {declarationColor : CostStaticColor} {leftPattern rightPattern : Pattern}
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (notLeftCollapsing : ¬ CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl) leftPattern)
    (notRightCollapsing : ¬ CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl) rightPattern) :
    CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern))
      leftPattern rightPattern := by
  rcases canonicalize_eq_root_cases _ canonical with
    leftCollapsing | rightCollapsing | aligned
  · exact absurd leftCollapsing notLeftCollapsing
  · exact absurd rightCollapsing notRightCollapsing
  · exact canonicalStopAligned_of_root_aligned _ aligned

/-- **The gate is an equivalence.**  Together with
`not_canonicalStopAligned_endpoints_of_collapsing` this pins the measure of
both apex-slice obligations: the aligned arm may run at the endpoint pair
because its roots are aligned, and the collapsing arms may not. -/
theorem rhoCanonicalStopAligned_endpoints_iff_not_collapsing
    {declarationColor : CostStaticColor} {leftPattern rightPattern : Pattern}
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CanonicalStopAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))
        leftPattern rightPattern ↔
      (¬ CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern ∧
        ¬ CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) := by
  constructor
  · intro aligned
    exact ⟨fun collapsing =>
        not_canonicalStopAligned_endpoints_of_collapsing (Or.inl collapsing)
          aligned,
      fun collapsing =>
        not_canonicalStopAligned_endpoints_of_collapsing (Or.inr collapsing)
          aligned⟩
  · intro notCollapsing
    exact rhoCanonicalStopAligned_endpoints_of_not_collapsing canonical
      notCollapsing.1 notCollapsing.2

/-! ## The plan-stop apex at the declaration's own colour -/

/-- **The step discharges the same-colour plan-stop apex at any raw stop.**

A canonical plan stop retains its raw alignment at the selected payloads, and
`CanonicalStopAligned.canonicalize_eq` turns that alignment into canonical
equality of the payloads whenever the raw stop relation carries canonical
equality.  The payloads are well-sorted by their own raw admissions and their
common target type is admissible along the retained type route, so
`RhoCanonicalPairRecursiveResult.nonempty_of_step` applies to the payload pair
directly.  Its retained action is then instantiated in the current parent
cospan by `reachedApex_sameColor`.

Nothing here uses the stop's size bounds, so the raw stop's parent measure is
irrelevant: the same proof serves the endpoint measure and the successor
measure. -/
theorem rhoStaticPlanStopCommonApex_sameColor_of_recursiveStep
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor)
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView declarationColor)
    (rightView : right.StaticRootView declarationColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    {rawStop : Pattern → Pattern → Prop}
    (stopCanonical : ∀ {stopLeft stopRight : Pattern}, rawStop stopLeft stopRight →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) stopLeft =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) stopRight) :
    RhoStaticPlanStopCommonApex leftView rightView declarationColor rawStop := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    stopped
  rcases stopped with
    ⟨leftPayload, rightPayload, leftReached, rightReached, leftAdmission,
      rightAdmission, leftAbstractEq, rightAbstractEq, sourceTypeEq,
      sourceAvailableEq, sourceBoundEq, targetBoundEq, thinningEq, leftEmbedding,
      rightEmbedding, leftRoute, rightRoute, _stopReason, _leftPayloadSizeLe,
      _rightPayloadSizeLe, rawAligned⟩
  have canonical := rawAligned.canonicalize_eq
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation) stopCanonical
  obtain ⟨rightRoute'⟩ := rightRoute
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
        leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftReached.sourceAvailable
      (mapTypeExpr (declarationColor.symbols rhoCIGSLT) leftReached.sourceType)
      rightPayload := by
    rw [sourceAvailableEq, sourceTypeEq]
    exact rightAdmission.wellSorted
  obtain ⟨result⟩ := RhoCanonicalPairRecursiveResult.nonempty_of_step step
    (outer := []) childAdmissible leftAdmission.wellSorted rightWellSorted
    canonical
  exact result.reachedApex_sameColor leftView rightView callbackAvailable
    callbackScope callbackRoot leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    ⟨rightRoute'⟩

/-! ## The two apex-slice obligations, reduced to their foreign-colour halves

Both reductions keep the foreign-colour half as an explicit hypothesis of
exactly the shape the obligation asks for at `color ≠ declarationColor`.  That
hypothesis is *not* discharged here and is not known to be inhabited; the
`RhoStaticNonBoundaryPlanStopCommonApex.AfterSameColorBoundarySideForeign`
residual is the live obligation behind it. -/

/-- **A1′ from the recursive step and the foreign-colour half.**

The aligned arm's raw stop is measured at the endpoint pair, and its stops
carry canonical equality in their second component, so the same-colour half is
exactly `rhoStaticPlanStopCommonApex_sameColor_of_recursiveStep`.  The
provider's own recursion callback `RhoPairCloseSmaller` is not consumed at all
in that half: the step's closure is stronger and needs no budget. -/
theorem rhoAlignedViewsPlanStopApexInDomain_of_recursiveStep
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor)
    (foreignViews : ∀ {targetFree : FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      color ≠ declarationColor →
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      CanonicalRootAligned
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern rightPattern →
      RhoStaticPlanStopCommonApex leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))) :
    RhoAlignedViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller roots
  by_cases sameColor : color = declarationColor
  · subst sameColor
    exact rhoStaticPlanStopCommonApex_sameColor_of_recursiveStep step leftView
      rightView (rightRootAdmissible_of_admissible rightView admissible)
      (fun stopped => stopped.1.2)
  · exact foreignViews leftView rightView sameColor admissible leftWellSorted
      rightWellSorted closeSmaller roots

/-- **A2s′ from the recursive step and the foreign-colour half.**

The collapsing arms run one above the endpoint measure, because a collapsing
root is its own canonical stop
(`not_canonicalStopAligned_endpoints_of_collapsing`) and no descent exists at
the endpoint pair.  That gap is invisible here: the same-colour half consumes
no size budget, so the successor measure costs nothing over the endpoint
measure — the endpoint pair itself is closed by the step's own result at that
pair, not by a strictly smaller callback. -/
theorem rhoCollapsingViewsPlanStopApexInDomain_of_recursiveStep
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor)
    (foreignViews : ∀ {targetFree : FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      color ≠ declarationColor →
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
          (sizeOf leftPattern + sizeOf rightPattern + 1))) :
    RhoCollapsingViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller collapsing canonical
  by_cases sameColor : color = declarationColor
  · subst sameColor
    exact rhoStaticPlanStopCommonApex_sameColor_of_recursiveStep step leftView
      rightView (rightRootAdmissible_of_admissible rightView admissible)
      (fun stopped => stopped.1.2)
  · exact foreignViews leftView rightView sameColor admissible leftWellSorted
      rightWellSorted closeSmaller collapsing canonical

/-! ## What the step costs

The two reductions above are the *upper* half of the accounting.  The lower
half is recorded here, because it decides whether the step is a decomposition
of the apex-slice obligations or a strengthening of them. -/

/-- **The step subsumes the compact pair closure.**

`RhoCanonicalPairRecursiveResult.pair` is a full
`CostCanonicalPairElaboration`: two proof-relevant region trees together with
the hereditary normalization alignment between them.  Projecting it out of the
measure-free closure gives the static-root pair closure for rho outright, with
the static-root premise discarded.

So the step is not a sub-obligation of `RhoAlignedViewsPlanStopApexInDomain`
and `RhoCollapsingViewsPlanStopApexInDomain`.  It implies the pair closure that
those obligations exist to produce, at every canonical pair and at both root
cases — including the collapsing and cross-colour configurations that the
apex-slice obligations `RhoCollapsingCrossColorViewsRestorationAlignedInDomain`
and `RhoCollapsingLeafExposureInDomain` carry, and which no recursive descent
argument addresses. -/
theorem costCanonicalStaticPairClosedInDomain_of_recursiveStep
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor) :
    CostCanonicalStaticPairClosedInDomain rhoCanonicalRecursiveTypeDomain
      rhoHereditaryNormalizationKernel
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape
  obtain ⟨result⟩ := RhoCanonicalPairRecursiveResult.nonempty_of_step step
    admissible leftWellSorted rightWellSorted canonical
  exact ⟨result.pair⟩

/-- **The step's two independent halves.**

The compact pair and the retained semantic action share no proof content: the
former is the hereditary alignment, the latter the parent-cospan apex.  Neither
half is inhabited here; this records the exact residual shape of each, so that
partial progress on one is not mistaken for progress on the other. -/
theorem rhoCanonicalPairRecursiveStep_of_pairs_and_apexActions
    {declarationColor : CostStaticColor}
    (pairs : ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightPattern →
      Nonempty (CostCanonicalPairElaboration rhoCIGSLT
        rhoHereditaryNormalizationKernel targetFree available outer leftPattern
        rightPattern type))
    (apexActions : ∀ {targetFree : FreeTypeContext}
      {available : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr},
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightPattern →
      @RhoReachedPlanPairApexAction declarationColor targetFree available
        leftPattern rightPattern type) :
    RhoCanonicalPairRecursiveStep declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _closeSmaller
  obtain ⟨pair⟩ := pairs (outer := outer) admissible leftWellSorted
    rightWellSorted canonical
  exact ⟨⟨pair,
    apexActions admissible leftWellSorted rightWellSorted canonical⟩⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
