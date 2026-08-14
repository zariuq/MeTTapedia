import Mettapedia.GSLT.LanguageDef.CostSemanticAtomPatternLeafReification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesAvailableLeaf

/-!
# Matched rho apex from endpoint restoration alignment

An endpoint alignment is stated before the two finite semantic-atom
environments are reified into their common cospan.  Reifying its complete
structural certificate and then applying canonicalization naturality produces
the parent-level common restoration apex used by the static-pair provider.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan
open CostStaticRegionNode

namespace RhoStaticFramesRestorationAligned

/-- A proof-relevant alignment of the two keyed source frames transports to
the exact endpoint-frame certificate consumed by the matched semantic cut.

The source leaf premise is indexed by the local binder depth.  Constructor
mapping preserves that certificate structurally, and the two static views'
common target context makes ambient-binder reinsertion the same operation on
both endpoints. -/
noncomputable def ofSourceCanonicalAlignment
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (sourceAlignment :
      let leftValues := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory :=
        (leftView.node.semanticAtomEnvironment leftValues).1
      let rightInventory :=
        (rightView.node.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        leftInventory
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
        ∀ depth,
          ReflectiveContextSupport.RestoresTogether
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment
              (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
                (leftView.node.thinning.thickenAmbientBVars depth
                  (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
              (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
                (rightView.node.thinning.thickenAmbientBVars depth
                  (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
      PatternLeafAligned relation
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation leftView.node.targetBound.length 0
          (leftView.node.reifiedSourceFrame leftEnvironment).1)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1)) :
    RhoStaticFramesRestorationAligned leftView rightView := by
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
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let sourceRelation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ depth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.thinning.thickenAmbientBVars depth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.thinning.thickenAmbientBVars depth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  let mappedRelation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ depth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.thinning.thickenAmbientBVars depth leftLeaf))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.thinning.thickenAmbientBVars depth rightLeaf))
  have sourceAligned : PatternLeafAligned sourceRelation
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation leftView.node.targetBound.length 0
        (leftView.node.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation rightView.node.targetBound.length 0
        (rightView.node.reifiedSourceFrame rightEnvironment).1) := by
    exact sourceAlignment
  have mappedAligned : PatternLeafAligned mappedRelation
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation leftView.node.targetBound.length 0
          (leftView.node.reifiedSourceFrame leftEnvironment).1))
      (mapPattern (color.symbols rhoCIGSLT)
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1)) :=
    sourceAligned.mapPattern (color.symbols rhoCIGSLT)
      (fun related => related)
  have sameBound : leftView.node.targetBound = rightView.node.targetBound :=
    leftView.targetBound_eq_targetBound rightView
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using
      congrArg
        (fun targetBound =>
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            targetBound).thickenAmbientBVars depth pattern)
        sameBound
  have targetAligned : PatternLeafAligned
      (fun leftLeaf rightLeaf =>
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              leftLeaf)
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              rightLeaf))
      (leftView.node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
            rhoReflectivePresentation leftView.node.targetBound.length 0
            (leftView.node.reifiedSourceFrame leftEnvironment).1)))
      (rightView.node.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
            rhoReflectivePresentation rightView.node.targetBound.length 0
            (rightView.node.reifiedSourceFrame rightEnvironment).1))) := by
    rw [← thickenEq 0]
    exact mappedAligned.thickenAmbientBVars leftView.node.thinning
      (fun depth {left right} related => by
        rw [thickenEq depth right]
        exact related depth)
      0
  change PatternLeafAligned
    (fun leftLeaf rightLeaf =>
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            leftLeaf)
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            rightLeaf))
    (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment declaration)
    (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
      declaration)
  rw [canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize leftView.node
      leftEnvironment,
    canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize rightView.node
      rightEnvironment]
  exact targetAligned

end RhoStaticFramesRestorationAligned

namespace RhoMatchedStaticFramesApex

/-- Endpoint-frame restoration alignment supplies the exact common semantic
apex.  The only index transport is the established naturality of keyed
canonicalization under each leg of the semantic-key cospan. -/
noncomputable def ofRestorationAligned
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (alignment : RhoStaticFramesRestorationAligned leftView rightView) :
    RhoMatchedStaticFramesApex leftView rightView := by
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
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ReflectiveContextSupport.RestoresTogether
      rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot leftLeaf)
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          rightLeaf)
  have endpointAlignment : PatternLeafAligned relation
      (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
        declaration)
      (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
        declaration) := by
    exact alignment
  have commonAlignment : PatternLeafAligned
      (ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment)
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
          declaration))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
          declaration)) :=
    cospan.reifyPatternLeafAligned leftEnvironment.lookupAtom?
      rightEnvironment.lookupAtom? cospan.leftSlot cospan.rightSlot
      (fun related => related) endpointAlignment
  have leftCovered : leftEnvironment.Covers
      (leftView.node.reifyTargetFrame leftEnvironment) := by
    intro name membership
    exact leftView.node.reifyTargetFrame_atomCovered leftEnvironment name
      membership
  have rightCovered : rightEnvironment.Covers
      (rightView.node.reifyTargetFrame rightEnvironment) := by
    intro name membership
    exact rightView.node.reifyTargetFrame_atomCovered rightEnvironment name
      membership
  have leftNaturality :=
    leftEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.leftSlot cospan.leftCommutes declaration
      leftView.node.targetBound.length
      (leftView.node.reifyTargetFrame leftEnvironment) leftCovered
  have rightNaturality :=
    rightEnvironment.reifyWith_canonicalizeByAt_semanticPatternKeyAt cospan
      cospan.rightSlot cospan.rightCommutes declaration
      rightView.node.targetBound.length
      (rightView.node.reifyTargetFrame rightEnvironment) rightCovered
  have rawApex : CommonRestorationApex rhoCIGSLT cospan declaration
      leftView.node.targetBound.length
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
          declaration))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
          declaration)) :=
    .leafAligned commonAlignment
  exact CommonRestorationApex.reindex leftNaturality rightNaturality rawApex

end RhoMatchedStaticFramesApex

namespace RhoMatchedStaticFramesCut

/-- Endpoint restoration alignment constructs the matched-frame cut without
passing through representation-level canonical equality. -/
noncomputable def ofRestorationAligned
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (alignment : RhoStaticFramesRestorationAligned leftView rightView) :
    RhoMatchedStaticFramesCut leftView rightView :=
  .terminal
    (RhoMatchedStaticFramesApex.ofRestorationAligned leftView rightView
      alignment)

end RhoMatchedStaticFramesCut

namespace RhoCanonicalStaticPairSemanticCut

/-- The aligned provider arm from its exact proof-relevant endpoint
certificate.  No common-frame name equality is inferred. -/
noncomputable def matchedOfRestorationAligned
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (roots : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern rightPattern)
    (alignment : RhoStaticFramesRestorationAligned leftView rightView) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.aligned color leftView rightView roots) :=
  .matched leftView rightView roots
    (RhoMatchedStaticFramesCut.ofRestorationAligned leftView rightView
      alignment)

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
