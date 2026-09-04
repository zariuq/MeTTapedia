import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

namespace RhoReachedPlanPairCommonApex

/-- Turn an actual alignment of reached-plan abstracts into the exact root
cospan apex.  The two callbacks are precisely the recursive plan stops and
rigid variables exposed by that alignment. -/
noncomputable def ofAlignedAbstracts
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftAbstract rightAbstract : Pattern}
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned rhoReflectivePresentation stop
      leftAbstract rightAbstract)
    (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
      stop left right →
        let leftValues := leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let rightValues := rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)
        let leftInventory :=
          (leftView.node.semanticAtomEnvironment leftValues).1
        let rightInventory :=
          (rightView.node.semanticAtomEnvironment rightValues).1
        let leftEnvironment :=
          CostStaticAtomEnvironment.ofInventory leftInventory
        let rightEnvironment :=
          CostStaticAtomEnvironment.ofInventory rightInventory
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration := costStaticReflectivePresentationDecl
          rhoCIGSLT color rhoReflectivePresentation
        CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
          targetDeclaration rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (leftEnvironment.reify left)))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (canonicalizeByDepths
                  (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                  rhoReflectivePresentation availableDepth scopeDepth
                  (rightEnvironment.reify right))))))
    (mapFvar : ∀ availableDepth scopeDepth rootDepth name,
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment :=
        CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let targetDeclaration := costStaticReflectivePresentationDecl
        rhoCIGSLT color rhoReflectivePresentation
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration rootDepth
        (cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (leftEnvironment.reifyName name))))))
        (cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))))) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
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
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  have apex :=
    CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
      leftEnvironment rightEnvironment leftView.node.thinning
      (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
      (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
      rhoReflectivePresentation
      (fun availableDepth scopeDepth rootDepth {left right} stopped => by
        have endpoint := mapStop availableDepth scopeDepth rootDepth stopped
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (rightEnvironment.reify right)))).symm)
      (fun availableDepth scopeDepth rootDepth name => by
        have endpoint := mapFvar availableDepth scopeDepth rootDepth name
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _
          endpoint
        exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
          (thickenEq scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
                rhoReflectivePresentation availableDepth scopeDepth
                (.fvar (rightEnvironment.reifyName name))))).symm)
      aligned callbackAvailable callbackScope callbackRoot
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl _ apex
  exact congrArg (cospan.reifyRight rightEnvironment.lookupAtom?)
    (thickenEq callbackScope
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))))

end RhoReachedPlanPairCommonApex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
