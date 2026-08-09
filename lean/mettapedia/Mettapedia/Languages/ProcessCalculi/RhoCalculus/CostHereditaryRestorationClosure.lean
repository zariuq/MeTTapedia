import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms
import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical

/-!
# Restoration-level closure for rho static roots

Foreign boundary content may change a rigid free variable into another name,
a bound variable, or a structured restored value.  Comparing the
pre-restoration frames is therefore too strong.  This module closes the exact
hereditary root bridge from the weaker structural datum that canonical frames
are aligned outside explicit semantic leaves and that every selected leaf
pair restores equally at every binder depth.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Close two rho static roots whose canonical frames agree structurally
outside explicitly selected semantic leaves.

The leaf relation may connect a boundary variable with any restored pattern,
including a bound variable or structured value.  Its restoration premise is
depth-uniform, so the structural proof remains valid below ordinary binders
and reflective quote resets. -/
noncomputable def rhoStaticRootBridgeOfRestoredPatternLeafAlignedCanonicalFrame
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree leftColor
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree rightColor
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    {relation : Pattern → Pattern → Prop}
    (canonicalFramesAligned :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      PatternLeafAligned relation
        (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
            rhoReflectivePresentation))
        (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
            rhoReflectivePresentation)))
    (relatedLeavesRestore :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftLeaf rightLeaf}, relation leftLeaf rightLeaf → ∀ depth,
        ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              leftLeaf) =
          ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              rightLeaf)) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonRestoredCanonicalFrame leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  exact cospan.substituteAt_reifyWith_eq_of_patternLeafAligned
    leftEnvironment.lookupAtom? rightEnvironment.lookupAtom?
    cospan.leftSlot cospan.rightSlot rhoCIGSLT.costWholeReflectionProfile
    cospan.commonSupport cospan.commonAssignment relatedLeavesRestore
    canonicalFramesAligned leftNode.targetBound.length

/-- Eliminate a recursive common restoration apex into the exact hereditary
root bridge for two static rho nodes of one colour.

The apex may contain semantic-leaf alignments, rigid congruence below binders
or quotes, and parallel permutations at arbitrary nested positions.  Its
eliminator produces precisely the common-restoration equality consumed by the
existing packed root terminal. -/
noncomputable def rhoStaticRootBridgeOfCommonRestorationApex
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    (apex :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        declaration leftNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
            declaration))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
            declaration))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfCommonRestoredCanonicalFrame leftNode rightNode
    leftChildren rightChildren sameDepth
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  exact apex.restored_eq

/-- Close two rho static roots at the common restoration apex.

The frame premise remembers constructor and binder structure through
`FvarAligned`.  The atomic premise is quantified over depth, so it remains
valid through ordinary binders and reflective quote resets.  In particular,
the theorem does not require a boundary atom and a source-variable atom to
have equal provenance-bearing semantic keys. -/
noncomputable def rhoStaticRootBridgeOfRestoredFvarAlignedCanonicalFrame
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {leftOuter rightOuter : List TypeExpr}
    (leftNode : CostStaticRegionNode rhoCIGSLT leftColor targetFree)
    (rightNode : CostStaticRegionNode rhoCIGSLT rightColor targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree leftColor
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree rightColor
      rightNode.finiteBoundaryTable)
    (sameDepth : leftNode.targetBound.length = rightNode.targetBound.length)
    {relation : String → String → Prop}
    (canonicalFramesAligned :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      FvarAligned relation
        (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
            rhoReflectivePresentation))
        (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
          (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
            rhoReflectivePresentation)))
    (relatedAtomsRestore :
      let leftValues := leftChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightChildren.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
      let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
      let rightEnvironment :=
        CostStaticAtomEnvironment.ofInventory rightInventory
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftName rightName}, relation leftName rightName → ∀ depth,
        ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (.fvar leftName)) =
          ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
            cospan.commonSupport cospan.commonAssignment depth
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (.fvar rightName))) :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  let leftValues := leftChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory := (leftNode.semanticAtomEnvironment leftValues).1
  let rightInventory := (rightNode.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leafRelation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ depth,
      ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            leftLeaf) =
        ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
          cospan.commonSupport cospan.commonAssignment depth
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            rightLeaf)
  apply rhoStaticRootBridgeOfRestoredPatternLeafAlignedCanonicalFrame
    leftNode rightNode leftChildren rightChildren sameDepth
    (relation := leafRelation)
  · exact canonicalFramesAligned.toPatternLeafAligned fun namesRelated =>
      relatedAtomsRestore namesRelated
  · simp only
    intro leftLeaf rightLeaf restores depth
    exact restores depth

/-- Complete local certificate for the root change in which a retained
boundary occurrence on the left becomes a direct source variable on the
right.

The boundary child is selected by the context view's replayable finite
position.  Its equality with the direct variable is supplied by a genuine
hereditary child alignment.  The boundary may retain a nonempty target binder
support: because the restored value is a direct free variable, the generic
scoped-normal transport theorem proves that all support shifts are inert.
The final field records only structural agreement of the two parent canonical
frames around this one semantic atom. -/
structure RhoStoppedBoundarySourceVariableRootCertificate
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {payload leftRootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload leftRootAbstract leftNode.finiteBoundaryTable.entries)
    (index : Fin view.view.retainedEntries.length) : Type where
  sameDepth : leftNode.targetBound.length = rightNode.targetBound.length
  leftOccurrence : CostStaticFVarOccurrence leftNode.skeleton.1
  leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
    (view.view.retainedEntries.get index).boundary
  rightOccurrence : CostStaticFVarOccurrence rightNode.skeleton.1
  name : String
  rightNameEq : rightOccurrence.name = costRegionSourceVariableName name
  leftSlot : Fin
    (leftNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      leftChildren).atomCount
  leftSelected :
    (leftNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      leftChildren).slotOfName?
        leftOccurrence.name = some leftSlot
  rightSlot : Fin
    (rightNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      rightChildren).atomCount
  rightSelected :
    (rightNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      rightChildren).slotOfName?
        rightOccurrence.name = some rightSlot
  rightAvailable : List TypeExpr
  rightOuter : List TypeExpr
  rightType : TypeExpr
  rightTree : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
    (.fvar name) rightType
  childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
    rhoHereditaryNormalizationKernel targetFree
    (view.selectedTreeFromForest leftChildren index) rightTree
  rightNormal :
    (rightTree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = .fvar name
  canonicalFramesAligned :
    let leftEnvironment := leftNode.normalizationEnvironment
      rhoHereditaryStaticNormalizer leftChildren
    let rightEnvironment := rightNode.normalizationEnvironment
      rhoHereditaryStaticNormalizer rightChildren
    FvarAligned
      (fun leftName rightName =>
        leftName = leftEnvironment.atomName leftSlot ∧
          rightName = rightEnvironment.atomName rightSlot)
      (leftNode.canonicalizeReifiedTargetFrame leftEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))
      (rightNode.canonicalizeReifiedTargetFrame rightEnvironment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation))

namespace RhoStoppedBoundarySourceVariableRootCertificate

/-- Eliminate the complete stopped-to-reached certificate into the
shape-independent hereditary root bridge consumed by the tree-alignment
layer. -/
noncomputable def toRootBridge
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree}
    {leftChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable}
    {rightChildren : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable}
    {payload leftRootAbstract : Pattern}
    {view : CostStaticPlanContextInventoryView rhoCIGSLT color targetFree
      payload leftRootAbstract leftNode.finiteBoundaryTable.entries}
    {index : Fin view.view.retainedEntries.length}
    (certificate : RhoStoppedBoundarySourceVariableRootCertificate leftNode
      rightNode leftChildren rightChildren view index)
    {leftOuter rightOuter : List TypeExpr} :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
      (CostRegionTree.static (outer := leftOuter) leftNode leftChildren)
      (CostRegionTree.static (outer := rightOuter) rightNode rightChildren) := by
  apply rhoStaticRootBridgeOfRestoredFvarAlignedCanonicalFrame leftNode
    rightNode leftChildren rightChildren certificate.sameDepth
      certificate.canonicalFramesAligned
  dsimp only
  intro leftName rightName related depth
  rcases related with ⟨rfl, rfl⟩
  apply view.selectedBoundaryAtom_restoresAsSourceVariable_of_alignment_supportIndependent
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftChildren
    (leftNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      leftChildren)
    (rightNode.normalizationEnvironment rhoHereditaryStaticNormalizer
      rightChildren) index
    certificate.leftOccurrence certificate.leftNameEq
    certificate.rightOccurrence certificate.name certificate.rightNameEq
    certificate.leftSlot certificate.leftSelected certificate.rightSlot
    certificate.rightSelected
    certificate.rightTree certificate.childAlignment certificate.rightNormal
    depth

end RhoStoppedBoundarySourceVariableRootCertificate

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
