import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PROBE: equal canonicalized source frames give restoration alignment. -/
example {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (framesEq :
      canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
            (CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
          rhoReflectivePresentation.toReflectivePresentationDecl
          leftView.node.targetBound.length 0
          (leftView.node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)).1 =
        canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
          rhoReflectivePresentation.toReflectivePresentationDecl
          rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1)).1) :
    (keys : ∀ name, ∃ left right,
      (CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1).lookupAtom?
          name = some left ∧
      (CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1).lookupAtom?
          name = some right ∧
      (CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomKey left =
        (CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1).atomKey right) :
    RhoStaticFramesRestorationAligned leftView rightView := by
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment
  refine .leaf ?_
  rw [framesEq, leftView.targetBound_eq_targetBound rightView]
  intro depth
  rw [CostStaticAtomKeyCospan.reifyWith_eq_of_keyAgreement _ _ _ _ keys]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
