import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignResidualSpine

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open RhoStaticNonBoundaryPlanStopCommonApex

/-- A foreign residual needs callbacks only at genuine plan stops.  Rigid
free variables are routed with their occurrence evidence and discharged in
the fixed parent semantic environments. -/
theorem foreignResidual_of_provenancedStopCallback
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
                  (rightEnvironment.reify stopRight)))))) :
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
      (sourceStop := fun left right =>
        CostStaticPlanCanonicalStop leftReached.plan rightReached.plan
            rhoReflectivePresentation.toReflectivePresentationDecl
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            (RhoCanonicalRawStop declarationColor
              (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
            left right ∨
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
          · exact mapStop leftReached rightReached availableDepth scopeDepth
              rootDepth stopped
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
