import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesLeafClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesPositionalSupport

/-!
# Positional semantic leaves of matched rho frames

Exact ancestry of two final canonical occurrences determines the semantic
atoms selected in the two endpoint environments.  When both source positions
are stopped boundaries, recursive closure of the selected children supplies a
common restoration apex directly at those final occurrences.  Outer canonical
structure can therefore compose this result without rebuilding the raw plan
contexts around each stopped boundary.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

namespace CostStaticPlanStopped

/-- Close two stopped boundaries at the exact canonical occurrences which
selected them.

The occurrence tokens determine the environment slots and both output names.
The three possible support regimes are derived from positional availability;
the caller supplies only the genuinely recursive child closure data. -/
noncomputable def selectedCanonicalOccurrences_commonRestorationApex_of_closeSmaller
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
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      apexDeclaration depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar leftTarget.name))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar rightTarget.name)) := by
  let leftAtRoot := leftStopped.castRoot leftNode.skeleton_pattern.symm
  let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
  let leftEmbedding := leftView.stoppedEntryEmbedding leftStopped leftViewEq
    leftNode.skeleton_pattern.symm
  let rightEmbedding := rightView.stoppedEntryEmbedding rightStopped rightViewEq
    rightNode.skeleton_pattern.symm
  have leftDecorationOccurrenceEq :=
    boundaryOccurrence_cast_eq_of_fvarContextInventoryView leftNode
      leftInventory leftAlignment.sourcePosition leftView leftStopped leftViewEq
  have rightDecorationOccurrenceEq :=
    boundaryOccurrence_cast_eq_of_fvarContextInventoryView rightNode
      rightInventory rightAlignment.sourcePosition rightView rightStopped
        rightViewEq
  have leftOccurrenceEq : leftAtRoot.boundaryOccurrence =
      (leftInventory.occurrenceAt
        leftAlignment.sourcePosition).fvarOccurrence :=
    stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      leftNode leftInventory leftAlignment.sourcePosition leftView leftStopped
        leftViewEq
  have rightOccurrenceEq : rightAtRoot.boundaryOccurrence =
      (rightInventory.occurrenceAt
        rightAlignment.sourcePosition).fvarOccurrence :=
    stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      rightNode rightInventory rightAlignment.sourcePosition rightView
        rightStopped rightViewEq
  have supportCase := targetSupports_eq_or_sealed_of_alignment
    leftAlignment rightAlignment leftStopped rightStopped
      leftDecorationOccurrenceEq rightDecorationOccurrenceEq leftAmbientEq
      rightAmbientEq targetAvailableEq
  obtain ⟨leftSlot, leftSelected⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence
        leftAtRoot.boundaryOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence
        rightAtRoot.boundaryOccurrence)
  have leftSourceEq : leftAtRoot.boundaryOccurrence =
      leftAlignment.sourceOccurrence :=
    leftOccurrenceEq.trans leftAlignment.position_eq
  have rightSourceEq : rightAtRoot.boundaryOccurrence =
      rightAlignment.sourceOccurrence :=
    rightOccurrenceEq.trans rightAlignment.position_eq
  have leftNameEq : leftEnvironment.atomName leftSlot = leftTarget.name := by
    calc
      leftEnvironment.atomName leftSlot =
          (leftEnvironment.reifyOccurrence
            leftAtRoot.boundaryOccurrence).name :=
        (leftEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          leftAtRoot.boundaryOccurrence leftSlot leftSelected).symm
      _ = (leftEnvironment.reifyOccurrence
            leftAlignment.sourceOccurrence).name := by rw [leftSourceEq]
      _ = leftAlignment.reifiedOccurrence.name := by
        rw [leftAlignment.reified_eq]
      _ = leftTarget.name := leftAlignment.canonical_name_eq
  have rightNameEq : rightEnvironment.atomName rightSlot = rightTarget.name := by
    calc
      rightEnvironment.atomName rightSlot =
          (rightEnvironment.reifyOccurrence
            rightAtRoot.boundaryOccurrence).name :=
        (rightEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          rightAtRoot.boundaryOccurrence rightSlot rightSelected).symm
      _ = (rightEnvironment.reifyOccurrence
            rightAlignment.sourceOccurrence).name := by rw [rightSourceEq]
      _ = rightAlignment.reifiedOccurrence.name := by
        rw [rightAlignment.reified_eq]
      _ = rightTarget.name := rightAlignment.canonical_name_eq
  let leaf := selectedAtoms_commonRestorationApex_of_closeSmaller
    leftAtRoot rightAtRoot leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected (by simpa [leftAtRoot, rightAtRoot] using supportCase)
      (by simpa [leftAtRoot, rightAtRoot] using typeEq)
      childDeclaration apexDeclaration
      (by simpa [leftAtRoot, rightAtRoot] using canonical)
      parentMeasure (by simpa [leftAtRoot, rightAtRoot] using smaller)
      (by simpa [rightAtRoot] using rightAdmissible) closeSmaller depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          leftEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
          (.fvar name)) leftNameEq)
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          rightEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
          (.fvar name)) rightNameEq)
    leaf

end CostStaticPlanStopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
