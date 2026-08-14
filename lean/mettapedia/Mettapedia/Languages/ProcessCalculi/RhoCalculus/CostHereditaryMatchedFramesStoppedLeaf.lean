import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesPositionalSupport

/-!
# Positional closure of stopped rho frame leaves

Two aligned canonical occurrences may reflect to stopped boundaries in their
respective static plans.  This file derives the exact parent-table embeddings,
semantic-environment selections, and support regime from those positional
certificates, then invokes the recursive boundary closure at the transported
authored roots.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

namespace CostStaticPlanStopped

/-- Close a stopped/stopped pair selected by exact canonical-occurrence
ancestry.

The caller supplies the genuinely semantic data: equality of the selected
child canonical forms and types, strict descent, recursive child closure, and
alignment of the two surrounding restoration contexts.  Exact occurrence
selection, singleton table embeddings, semantic slots, and the three rho
support regimes are derived here. -/
noncomputable def selectedNodeRoots_commonRestorationApex_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftNode leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)}
    {rightTarget : CostStaticFVarOccurrence
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightNode rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1)}
    {ambient : List TypeExpr}
    (leftAlignment :
      RhoCanonicalInventoryOccurrenceAlignmentCertificate leftNode
        leftEnvironment leftTarget ambient)
    (rightAlignment :
      RhoCanonicalInventoryOccurrenceAlignmentCertificate rightNode
        rightEnvironment rightTarget ambient)
    (leftView : CostStaticPlanFVarContextInventoryView leftNode.plan
      (planAbstractOccurrenceAt leftNode leftInventory
        leftAlignment.sourcePosition))
    (rightView : CostStaticPlanFVarContextInventoryView rightNode.plan
      (planAbstractOccurrenceAt rightNode rightInventory
        rightAlignment.sourcePosition))
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      leftView.rawPayload leftNode.plan.abstractPattern)
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightView.rawPayload rightNode.plan.abstractPattern)
    (leftViewEq : leftView.inventory.view = .stopped leftStopped)
    (rightViewEq : rightView.inventory.view = .stopped rightStopped)
    (leftAmbientEq : ambient = leftNode.targetBound)
    (rightAmbientEq : ambient = rightNode.targetBound)
    (targetAvailableEq :
      rhoCanonicalOccurrenceAvailable ambient leftTarget.context =
        rhoCanonicalOccurrenceAvailable ambient rightTarget.context)
    (typeEq : leftStopped.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType)
    (childDeclaration apexDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration leftStopped.certified.typed.boundary.content =
        canonicalize childDeclaration
          rightStopped.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild < parentMeasure →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (depth holeDepth : Nat)
    (contexts :
      let leftAtRoot := leftStopped.castRoot leftNode.skeleton_pattern.symm
      let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan apexDeclaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          leftAtRoot.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          rightAtRoot.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      apexDeclaration depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftNode.skeleton.1))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightNode.skeleton.1)) := by
  let leftAtRoot := leftStopped.castRoot leftNode.skeleton_pattern.symm
  let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
  let leftEmbedding := leftView.stoppedEntryEmbedding leftStopped leftViewEq
    leftNode.skeleton_pattern.symm
  let rightEmbedding := rightView.stoppedEntryEmbedding rightStopped rightViewEq
    rightNode.skeleton_pattern.symm
  have leftOccurrenceEq :=
    boundaryOccurrence_cast_eq_of_fvarContextInventoryView leftNode
      leftInventory leftAlignment.sourcePosition leftView leftStopped leftViewEq
  have rightOccurrenceEq :=
    boundaryOccurrence_cast_eq_of_fvarContextInventoryView rightNode
      rightInventory rightAlignment.sourcePosition rightView rightStopped
        rightViewEq
  have supportCase := targetSupports_eq_or_sealed_of_alignment
    leftAlignment rightAlignment leftStopped rightStopped leftOccurrenceEq
      rightOccurrenceEq leftAmbientEq rightAmbientEq targetAvailableEq
  have leftAtRootOccurrence : leftAtRoot.boundaryOccurrence =
      (leftInventory.occurrenceAt leftAlignment.sourcePosition).fvarOccurrence :=
    stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      leftNode leftInventory leftAlignment.sourcePosition leftView leftStopped
        leftViewEq
  have rightAtRootOccurrence : rightAtRoot.boundaryOccurrence =
      (rightInventory.occurrenceAt rightAlignment.sourcePosition).fvarOccurrence :=
    stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      rightNode rightInventory rightAlignment.sourcePosition rightView
        rightStopped rightViewEq
  obtain ⟨leftSlot, leftSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence
        (leftInventory.occurrenceAt
          leftAlignment.sourcePosition).fvarOccurrence)
  obtain ⟨rightSlot, rightSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence
        (rightInventory.occurrenceAt
          rightAlignment.sourcePosition).fvarOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      leftAtRoot.boundaryOccurrence.name = some leftSlot := by
    simpa only [leftAtRootOccurrence] using leftSelectedAtOccurrence
  have rightSelected : rightEnvironment.slotOfName?
      rightAtRoot.boundaryOccurrence.name = some rightSlot := by
    simpa only [rightAtRootOccurrence] using rightSelectedAtOccurrence
  exact selectedRoots_commonRestorationApex_of_closeSmaller leftAtRoot
    rightAtRoot leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected
      rightSlot rightSelected (by
        simpa [leftAtRoot, rightAtRoot] using supportCase) (by
        simpa [leftAtRoot, rightAtRoot] using typeEq)
      childDeclaration apexDeclaration (by
        simpa [leftAtRoot, rightAtRoot] using canonical)
      parentMeasure (by
        simpa [leftAtRoot, rightAtRoot] using smaller) (by
        simpa [rightAtRoot] using rightAdmissible) closeSmaller depth holeDepth
      contexts

end CostStaticPlanStopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
