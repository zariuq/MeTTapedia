import Mettapedia.GSLT.LanguageDef.CostFvarAlignedCanonicalization
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomPatternLeafReification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical

/-!
# Rho source-frame key agreement

Two same-colour static endpoints use independently constructed semantic-atom
environments.  Their source canonicalizers therefore have different ordering
functions.  This module isolates the exact bridge: a positional name relation
must prove both endpoint-local restoration equality (for ordering) and common-
cospan restoration equality (for the eventual semantic cut).
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Endpoint-local restoration equality makes the two semantic ordering keys
agree on any structurally aligned source subframes. -/
theorem sourceSemanticPatternKeyAt_eq_of_fvarAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    {nameRelation : String → String → Prop}
    (leafRestores : ∀ {leftName rightName},
      nameRelation leftName rightName → ∀ depth,
        leftEnvironment.restoreAt depth (.fvar leftName) =
          rightEnvironment.restoreAt depth (.fvar rightName))
    {leftPattern rightPattern : Pattern}
    (aligned : FvarAligned nameRelation leftPattern rightPattern)
    (availableDepth scopeDepth : Nat) :
    sourceSemanticPatternKeyAt leftNode leftEnvironment availableDepth
        scopeDepth leftPattern =
      sourceSemanticPatternKeyAt rightNode rightEnvironment availableDepth
        scopeDepth rightPattern := by
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftNode.thinning.thickenAmbientBVars depth pattern =
        rightNode.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using
      congrArg
        (fun targetBound =>
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            targetBound).thickenAmbientBVars depth pattern)
        sameBound
  have mapped : FvarAligned nameRelation
      (mapPattern (color.symbols rhoCIGSLT) leftPattern)
      (mapPattern (color.symbols rhoCIGSLT) rightPattern) :=
    aligned.mapPattern (color.symbols rhoCIGSLT)
  have thickened : FvarAligned nameRelation
      (leftNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT) leftPattern))
      (leftNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT) rightPattern)) :=
    mapped.thickenAmbientBVars leftNode.thinning scopeDepth
  unfold sourceSemanticPatternKeyAt
  unfold Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
  apply congrArg Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
  unfold CostStaticAtomEnvironment.restoreAt
  rw [← thickenEq scopeDepth
    (mapPattern (color.symbols rhoCIGSLT) rightPattern)]
  exact thickened.substituteAt_eq rhoCIGSLT.costWholeReflectionProfile
    leftEnvironment.restorationSupport rightEnvironment.restorationSupport
    leftEnvironment.restorationAssignment rightEnvironment.restorationAssignment
    (fun related depth => leafRestores related depth) availableDepth

/-- A rigid source-frame alignment can be canonicalized with endpoint-local
semantic keys and then weakened to the semantic-leaf certificate consumed by
the source-to-target restoration reducer.

The name token controls both callbacks.  No callback conclusion contains an
independently quantified name. -/
noncomputable def sourceCanonicalPatternLeafAligned_of_fvarAligned
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    {nameRelation : String → String → Prop}
    (endpointRestores : ∀ {leftName rightName},
      nameRelation leftName rightName → ∀ depth,
        leftEnvironment.restoreAt depth (.fvar leftName) =
          rightEnvironment.restoreAt depth (.fvar rightName))
    (commonRestores :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftName rightName}, nameRelation leftName rightName →
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (.fvar leftName))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (.fvar rightName)))
    (rawAligned : FvarAligned nameRelation
      (leftNode.reifiedSourceFrame leftEnvironment).1
      (rightNode.reifiedSourceFrame rightEnvironment).1) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftNode leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightNode rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ sourceDepth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightNode.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  have depthEq : leftNode.targetBound.length = rightNode.targetBound.length :=
    congrArg List.length sameBound
  rw [← depthEq]
  have canonicalAligned := rawAligned.canonicalizeByDepths
    (sourceSemanticPatternKeyAt leftNode leftEnvironment)
    (sourceSemanticPatternKeyAt rightNode rightEnvironment)
    rhoReflectivePresentation
    (fun availableDepth scopeDepth _ _ aligned =>
      sourceSemanticPatternKeyAt_eq_of_fvarAligned leftEnvironment
        rightEnvironment sameBound endpointRestores aligned availableDepth
          scopeDepth)
    leftNode.targetBound.length 0
  apply canonicalAligned.toPatternLeafAligned
  intro leftName rightName related sourceDepth
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars] using
      commonRestores related

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
