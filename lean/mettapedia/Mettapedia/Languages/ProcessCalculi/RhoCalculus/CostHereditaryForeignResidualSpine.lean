import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryResidualSwitchboard
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopFvarAbsorption

/-!
# The foreign residual reduced to the two root-cospan callbacks

`AfterSameColorBoundarySideForeign` is the surviving half of the residual
switchboard: its same-colour half is refuted by `not_sameColorResidual`, and
`afterSameColorBoundarySide_of_foreign` discharges the switchboard from it.

This module supplies the spine that connects it to the apex producer.  Two
results in the tree were proved and had **no consumers at all**:

* `rhoReachedPlan_canonicalStopAligned_of_rawAligned`, which transports the
  payload-level raw alignment the residual carries to an abstract-level
  alignment under *any* chosen declaration;
* `RhoReachedPlanPairCommonApex.ofAlignedAbstracts`, which turns an
  abstract-level alignment into the root cospan apex, given two callbacks.

Choosing the *uncoloured* `rhoReflectivePresentation` in the first makes its
conclusion exactly the input of the second.  The residual's remaining content
is therefore precisely those two callbacks and nothing else — no plan
descent, no size arithmetic, no colour reasoning survives the reduction.

Both callbacks quantify over `availableDepth`, `scopeDepth` and `rootDepth`
**independently**, which is what makes the apex lane usable here: an apex at
three free depths is exactly the shape of
`CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`.

## Status

`rho_afterSameColorBoundarySideForeign_of_callbacks` is a *reduction*, not a
closure: its two hypotheses are not inhabited here, and it must not be
counted as progress on the residual until they are.  What it does establish
is that nothing else remains.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open RhoStaticNonBoundaryPlanStopCommonApex

namespace RhoReachedPlanPairCommonApex

/-- Turn an alignment of reached-plan abstracts into the fixed parent-cospan
apex while routing rigid free variables through occurrence evidence in both
parent skeletons.  The callback is consulted only at genuine plan stops. -/
noncomputable def ofProvenancedAlignedAbstracts
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned
      rhoReflectivePresentation.toReflectivePresentationDecl stop
      leftReached.plan.abstractPattern rightReached.plan.abstractPattern)
    (mapStop : ∀ availableDepth scopeDepth rootDepth {stopLeft stopRight},
      stop stopLeft stopRight →
        let leftEnvironment := CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let rightEnvironment := CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    leftView.node leftEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (leftEnvironment.reify stopLeft)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (rightEnvironment.reify stopRight)))))) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have leftAbstractInRoot : ∀ name,
      name ∈ leftReached.plan.abstractPattern.freeFvarNames →
        name ∈ leftView.node.skeleton.1.freeFvarNames := by
    intro name membership
    rw [leftView.node.skeleton_pattern, leftReached.abstract_eq]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      leftReached.skeletonContext membership
  have rightAbstractInRoot : ∀ name,
      name ∈ rightReached.plan.abstractPattern.freeFvarNames →
        name ∈ rightView.node.skeleton.1.freeFvarNames := by
    intro name membership
    rw [rightView.node.skeleton_pattern, rightReached.abstract_eq]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      rightReached.skeletonContext membership
  have routed := CanonicalStopAligned.routeFVars aligned
    (leftRootFree := leftView.node.skeleton.1.freeFvarNames)
    (rightRootFree := rightView.node.skeleton.1.freeFvarNames)
    leftAbstractInRoot rightAbstractInRoot
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  have apex :=
    CanonicalStopRouted.environmentMapThickenCanonicalizeCommonApexByDepths
      leftEnvironment rightEnvironment leftView.node.thinning
      (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
        leftEnvironment)
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
        rightEnvironment)
      rhoReflectivePresentation.toReflectivePresentationDecl
      (sourceStop := fun left right => stop left right ∨
        MemberFVarPair leftView.node.skeleton.1.freeFvarNames
          rightView.node.skeleton.1.freeFvarNames left right)
      (fun availableDepth scopeDepth rootDepth {left right} stopped => by
        have endpointApex : CostStaticAtomKeyCospan.CommonRestorationApex
            rhoCIGSLT cospan targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (leftView.node.thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (canonicalizeByDepths
                    (CostStaticRegionNode.sourceSemanticPatternKeyAt
                      leftView.node leftEnvironment)
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    availableDepth scopeDepth
                    (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (rightView.node.thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (canonicalizeByDepths
                    (CostStaticRegionNode.sourceSemanticPatternKeyAt
                      rightView.node rightEnvironment)
                    rhoReflectivePresentation.toReflectivePresentationDecl
                    availableDepth scopeDepth
                    (rightEnvironment.reify right))))) := by
          rcases stopped with stopped | ⟨name, leftEq, rightEq,
            leftMembership, rightMembership⟩
          · exact mapStop availableDepth scopeDepth rootDepth stopped
          · subst leftEq
            subst rightEq
            have memberApex := memberFVar_commonRestorationApex
              leftView.node rightView.node leftView.children rightView.children
              leftEnvironment rightEnvironment name leftMembership
              rightMembership targetDeclaration rootDepth
            simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
              canonicalizeByDepths, mapPattern,
              CostStaticBinderThinning.thickenAmbientBVars,
              CostStaticAtomKeyCospan.reifyLeft,
              CostStaticAtomKeyCospan.reifyRight, targetDeclaration,
              costStaticReflectivePresentationDecl_eq_map] using memberApex
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpointApex
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt
                  rightView.node rightEnvironment)
                rhoReflectivePresentation.toReflectivePresentationDecl
                availableDepth scopeDepth
                (rightEnvironment.reify right)))).symm)
      routed callbackAvailable callbackScope callbackRoot
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _ apex
  exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
    (thickenEq callbackScope
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          callbackAvailable callbackScope
          (rightEnvironment.reify rightReached.plan.abstractPattern))))

end RhoReachedPlanPairCommonApex

/-- **The foreign residual from the two root-cospan callbacks.**

The abstract-level alignment is manufactured from the residual's own
hypotheses; the callbacks are the exact `mapStop` and `mapFvar` of
`RhoReachedPlanPairCommonApex.ofAlignedAbstracts`, at the stop relation the
transport produces. -/
theorem rho_afterSameColorBoundarySideForeign_of_callbacks
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (mapStop : ∀ {leftPayload rightPayload : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern),
      ∀ availableDepth scopeDepth rootDepth {stopLeft stopRight},
        CostStaticPlanCanonicalStop leftReached.plan rightReached.plan
            rhoReflectivePresentation.toReflectivePresentationDecl
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            (RhoCanonicalRawStop declarationColor
              (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
            stopLeft stopRight →
        let leftEnvironment := CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let rightEnvironment := CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    leftView.node leftEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (leftEnvironment.reify stopLeft)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (rightEnvironment.reify stopRight))))))
    (mapFvar : ∀ availableDepth scopeDepth rootDepth name,
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation)
        rootDepth
        (cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt
                  leftView.node leftEnvironment)
                rhoReflectivePresentation.toReflectivePresentationDecl
                availableDepth scopeDepth
                (.fvar (leftEnvironment.reifyName name))))))
        (cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt
                  rightView.node rightEnvironment)
                rhoReflectivePresentation.toReflectivePresentationDecl
                availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))))) :
    AfterSameColorBoundarySideForeign leftView rightView declarationColor := by
  intro _foreign callbackAvailable callbackScope callbackRoot leftAbstract
    rightAbstract leftPayload rightPayload leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq _leftEmbedding
    _rightEmbedding _leftRoute _rightRoute _stopReason _leftPayloadSizeLe
    _rightPayloadSizeLe rawAligned _notBothBoundary
  have aligned := rhoReachedPlan_canonicalStopAligned_of_rawAligned
    leftReached rightReached leftAdmission rightAdmission sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    rhoReflectivePresentation.toReflectivePresentationDecl
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    rawAligned
  subst leftAbstractEq
  subst rightAbstractEq
  exact RhoReachedPlanPairCommonApex.ofAlignedAbstracts leftView rightView
    callbackAvailable callbackScope callbackRoot aligned
    (mapStop leftReached rightReached) mapFvar

/-! ## One callback instead of two

`reify` sends `.fvar name` to `.fvar (reifyName name)` definitionally, which
is precisely the endpoint shape of the fvar callback.  So once the descent's
matched free variables are absorbed into the stop relation
(`CanonicalStopAligned.absorbFvars`), the fvar callback is no longer an
independent obligation: it is the stop callback applied to the matched-pair
arm of `StopWithFvars`.

The residual therefore rests on a **single** callback. -/

/-- **The foreign residual from one stop callback.**

Same reduction as `rho_afterSameColorBoundarySideForeign_of_callbacks`, with
the fvar obligation eliminated rather than assumed. -/
theorem rho_afterSameColorBoundarySideForeign_of_stopCallback
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (mapStop : ∀ {leftPayload rightPayload : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern),
      ∀ availableDepth scopeDepth rootDepth {stopLeft stopRight},
        StopWithFvars
            (CostStaticPlanCanonicalStop leftReached.plan rightReached.plan
              rhoReflectivePresentation.toReflectivePresentationDecl
              (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
                rhoReflectivePresentation)
              (RhoCanonicalRawStop declarationColor
                (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)))
            stopLeft stopRight →
        let leftEnvironment := CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let rightEnvironment := CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    leftView.node leftEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (leftEnvironment.reify stopLeft)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (rightEnvironment.reify stopRight)))))) :
    AfterSameColorBoundarySideForeign leftView rightView declarationColor := by
  intro _foreign callbackAvailable callbackScope callbackRoot leftAbstract
    rightAbstract leftPayload rightPayload leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq _leftEmbedding
    _rightEmbedding _leftRoute _rightRoute _stopReason _leftPayloadSizeLe
    _rightPayloadSizeLe rawAligned _notBothBoundary
  have aligned := (rhoReachedPlan_canonicalStopAligned_of_rawAligned
    leftReached rightReached leftAdmission rightAdmission sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    rhoReflectivePresentation.toReflectivePresentationDecl
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    rawAligned).absorbFvars
  subst leftAbstractEq
  subst rightAbstractEq
  exact RhoReachedPlanPairCommonApex.ofAlignedAbstracts leftView rightView
    callbackAvailable callbackScope callbackRoot aligned
    (mapStop leftReached rightReached)
    (fun availableDepth scopeDepth rootDepth name => by
      simpa only [CostStaticAtomEnvironment.reify] using
        mapStop leftReached rightReached availableDepth scopeDepth rootDepth
          (Or.inr ⟨name, rfl, rfl⟩))

/-- **The foreign residual from a provenance-correct stop callback.**

Unlike the `StopWithFvars` reduction, this statement never asks for a
semantic action at an arbitrary string.  Rigid variables exposed by the
abstract alignment are routed with proofs that they occur in both parent
skeletons and are discharged by the existing member-variable apex. -/
theorem rho_afterSameColorBoundarySideForeign_of_provenancedStopCallback
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (mapStop : ∀ {leftPayload rightPayload : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1),
      ∀ availableDepth scopeDepth rootDepth {stopLeft stopRight},
        CostStaticPlanCanonicalStop leftReached.plan rightReached.plan
            rhoReflectivePresentation.toReflectivePresentationDecl
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            (RhoCanonicalRawStop declarationColor
              (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
            stopLeft stopRight →
        let leftEnvironment := CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let rightEnvironment := CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    leftView.node leftEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (leftEnvironment.reify stopLeft)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (CostStaticRegionNode.sourceSemanticPatternKeyAt
                    rightView.node rightEnvironment)
                  rhoReflectivePresentation.toReflectivePresentationDecl
                  availableDepth scopeDepth
                  (rightEnvironment.reify stopRight)))))) :
    AfterSameColorBoundarySideForeign leftView rightView declarationColor := by
  intro _foreign callbackAvailable callbackScope callbackRoot leftAbstract
    rightAbstract leftPayload rightPayload leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute _stopReason leftPayloadSizeLe
    rightPayloadSizeLe rawAligned _notBothBoundary
  have aligned := rhoReachedPlan_canonicalStopAligned_of_rawAligned
    leftReached rightReached leftAdmission rightAdmission sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    rhoReflectivePresentation.toReflectivePresentationDecl
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    rawAligned
  subst leftAbstractEq
  subst rightAbstractEq
  exact RhoReachedPlanPairCommonApex.ofProvenancedAlignedAbstracts leftView
    rightView callbackAvailable callbackScope callbackRoot leftReached
    rightReached aligned
      (mapStop leftReached rightReached leftEmbedding rightEmbedding leftRoute
        rightRoute leftPayloadSizeLe rightPayloadSizeLe)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
