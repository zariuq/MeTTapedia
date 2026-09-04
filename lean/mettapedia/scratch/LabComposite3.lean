import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem restorationAligned_of_framesEq_of_frameNames
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (framesEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
            leftEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          leftView.node.targetBound.length 0
          (leftView.node.reifiedSourceFrame leftEnvironment).1 =
        canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1)
    (names :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ name ∈ (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1).freeFvarNames,
        cospan.reifyNameWith leftEnvironment.lookupAtom? cospan.leftSlot name =
          cospan.reifyNameWith rightEnvironment.lookupAtom? cospan.rightSlot
            name) :
    RhoStaticFramesRestorationAligned leftView rightView := by
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment
  simp only at framesEq names
  refine .leaf ?_
  intro depth
  rw [framesEq, thickenEq depth,
    CostStaticAtomKeyCospan.reifyWith_eq_of_free _ _ _ _
      (fun name inThickened => names name (by
        rwa [CostStaticBinderThinning.thickenAmbientBVars_freeFvarNames,
          StructuralMorphism.mapPattern_freeFvarNames] at inThickened))]
  exact fun _ => rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
