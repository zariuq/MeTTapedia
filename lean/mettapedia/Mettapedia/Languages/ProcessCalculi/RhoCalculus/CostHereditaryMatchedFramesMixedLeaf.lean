import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesSourceVariableLeaf
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesLeafClosure

/-!
# Positional mixed leaves of matched rho frames

An exact canonical occurrence may originate at a stopped foreign boundary on
one endpoint and at an authored source variable on the other.  Recursive
closure compares the retained boundary content with that source variable.
Static-decomposition unambiguity then identifies the recursively chosen left
tree with the actual proof-relevant child retained by the parent forest.

The resulting restoration statement is quantified over every binder depth.
It does not identify the endpoint semantic keys: a stopped boundary may carry
a different support stamp from the authored variable even when both normalize
to the same free leaf.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Every proof-relevant elaboration of a free variable has that same free
variable as its hereditary normal form. -/
private theorem normalize_fvar_tree
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {name : String} {type : TypeExpr}
    (tree : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type) :
    (tree.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar name := by
  let view := tree.structuralRootView tree.rootIsStatic_eq_false_of_fvar
  cases view with
  | fvar lookup => simp [CostRegionTree.normalize]

/-- A final stopped-boundary occurrence on the left and an authored source
variable occurrence on the right have a common-restoration apex once their
raw child pair closes recursively.

The child canonical equality and strict size decrease are explicit inputs.
Equality of the two parent semantic values would be too weak: it loses both
the retained occurrence and the support component used by restoration. -/
noncomputable def boundarySourceCanonicalOccurrences_commonRestorationApex_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightNode.boundaryTable}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
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
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      leftView.rawPayload leftNode.plan.abstractPattern)
    (leftViewEq : leftView.inventory.view = .stopped leftStopped)
    (rightName : String)
    (rightOrigin :
      (planAbstractOccurrenceAt rightNode rightInventory
        rightAlignment.sourcePosition).name =
          costRegionSourceVariableName rightName)
    (rightLookup : targetFree rightName =
      some leftStopped.certified.typed.boundary.targetType)
    (childDeclaration apexDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration
          leftStopped.certified.typed.boundary.content =
        canonicalize childDeclaration (.fvar rightName))
    (parentMeasure : Nat)
    (smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf (Pattern.fvar rightName) < parentMeasure)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      leftStopped.certified.typed.boundary.targetType)
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
  let leftEmbedding := leftView.stoppedEntryEmbedding leftStopped leftViewEq
    leftNode.skeleton_pattern.symm
  have leftOccurrenceEq : leftAtRoot.boundaryOccurrence =
      leftAlignment.sourceOccurrence := by
    exact (stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      leftNode leftInventory leftAlignment.sourcePosition leftView leftStopped
        leftViewEq).trans leftAlignment.position_eq
  have rightSourceOrigin : rightAlignment.sourceOccurrence.name =
      costRegionSourceVariableName rightName := by
    rw [← rightAlignment.position_eq]
    simpa using rightOrigin
  obtain ⟨leftSlot, leftSelected⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence
        leftAtRoot.boundaryOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence
        rightAlignment.sourceOccurrence)
  have leftAtomName : leftEnvironment.atomName leftSlot = leftTarget.name := by
    calc
      leftEnvironment.atomName leftSlot =
          (leftEnvironment.reifyOccurrence
            leftAtRoot.boundaryOccurrence).name :=
        (leftEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          leftAtRoot.boundaryOccurrence leftSlot leftSelected).symm
      _ = (leftEnvironment.reifyOccurrence
            leftAlignment.sourceOccurrence).name := by rw [leftOccurrenceEq]
      _ = leftAlignment.reifiedOccurrence.name := by
        rw [leftAlignment.reified_eq]
      _ = leftTarget.name := leftAlignment.canonical_name_eq
  have rightAtomName : rightEnvironment.atomName rightSlot =
      rightTarget.name := by
    calc
      rightEnvironment.atomName rightSlot =
          (rightEnvironment.reifyOccurrence
            rightAlignment.sourceOccurrence).name :=
        (rightEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          rightAlignment.sourceOccurrence rightSlot rightSelected).symm
      _ = rightAlignment.reifiedOccurrence.name := by
        rw [rightAlignment.reified_eq]
      _ = rightTarget.name := rightAlignment.canonical_name_eq
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType
      leftAtRoot.certified.typed.boundary.content :=
    ⟨⟨leftAtRoot.certified.typed.contentTyped,
        leftAtRoot.certified.typed.contentCanonicalBinderMetadata,
        leftAtRoot.certified.typed.contentObjectPattern,
        leftAtRoot.certified.typed.contentTyped.isWellScopedAt⟩,
      leftAtRoot.certified.typed.contentReflectiveScopeSafe⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType (.fvar rightName) :=
    ⟨⟨WellSorted.HasType.fvar (by simpa [leftAtRoot] using rightLookup),
        rfl, rfl, rfl⟩,
      by
        intro presentation membership
        rfl⟩
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftWellSorted rightWellSorted
      (by simpa [leftAtRoot] using canonical)
      (by simpa [leftAtRoot] using smaller)
      (by simpa [leftAtRoot] using admissible))
  let selectedTree := leftAtRoot.selectedTreeFromForest leftEmbedding leftTrees
  have selectedToPair :
      (selectedTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel selectedTree pair.leftTree
      (by simpa [selectedTree, leftAtRoot] using
        leftAtRoot.certified.typed.contentObjectPattern)
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.alignment.normalize_pattern_eq
  have pairRightNormal :
      (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar rightName :=
    normalize_fvar_tree pair.rightTree
  have childNormal :
      (selectedTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel).1 = .fvar rightName := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToPair.trans (pairNormal.trans pairRightNormal)
  have leftAtom := leftAtRoot.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar rightName := by
    have normalEq := congrArg (fun atom => atom.key.normal) leftAtom
    have atomToChild : (leftEnvironment.atomValue leftSlot).key.normal =
        ((leftAtRoot.selectedTreeFromForest leftEmbedding leftTrees
          ).normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
    exact atomToChild.trans (by simpa only [selectedTree] using childNormal)
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar rightName := by
    rw [rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rightAlignment.sourceOccurrence rightSlot rightSelected,
      rightSourceOrigin]
    exact rightValues.assignment_sourceVariable rightName
  let leaf :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        apexDeclaration depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot)))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
    apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
    apply PatternLeafAligned.leaf
    intro leafDepth
    apply leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
      rightEnvironment leftSlot rightSlot (leftNormal.trans rightNormal.symm)
    rw [leftNormal]
    rfl
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          leftEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
          (.fvar name)) leftAtomName)
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          rightEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
          (.fvar name)) rightAtomName)
    leaf

/-- Symmetric positional mixed leaf: an authored source variable on the left
and an exact stopped boundary on the right share a common-restoration apex
once their raw child pair closes recursively. -/
noncomputable def sourceBoundaryCanonicalOccurrences_commonRestorationApex_of_closeSmaller
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
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
    (rightView : CostStaticPlanFVarContextInventoryView rightNode.plan
      (planAbstractOccurrenceAt rightNode rightInventory
        rightAlignment.sourcePosition))
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightView.rawPayload rightNode.plan.abstractPattern)
    (rightViewEq : rightView.inventory.view = .stopped rightStopped)
    (leftName : String)
    (leftOrigin :
      (planAbstractOccurrenceAt leftNode leftInventory
        leftAlignment.sourcePosition).name =
          costRegionSourceVariableName leftName)
    (leftLookup : targetFree leftName =
      some rightStopped.certified.typed.boundary.targetType)
    (childDeclaration apexDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration (.fvar leftName) =
        canonicalize childDeclaration
          rightStopped.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf (Pattern.fvar leftName) +
          sizeOf rightStopped.certified.typed.boundary.content < parentMeasure)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible
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
  let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
  let rightEmbedding := rightView.stoppedEntryEmbedding rightStopped
    rightViewEq rightNode.skeleton_pattern.symm
  have rightOccurrenceEq : rightAtRoot.boundaryOccurrence =
      rightAlignment.sourceOccurrence := by
    exact (stoppedBoundaryOccurrence_eq_inventory_of_fvarContextInventoryView
      rightNode rightInventory rightAlignment.sourcePosition rightView
        rightStopped rightViewEq).trans rightAlignment.position_eq
  have leftSourceOrigin : leftAlignment.sourceOccurrence.name =
      costRegionSourceVariableName leftName := by
    rw [← leftAlignment.position_eq]
    simpa using leftOrigin
  obtain ⟨leftSlot, leftSelected⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence
        leftAlignment.sourceOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence
        rightAtRoot.boundaryOccurrence)
  have leftAtomName : leftEnvironment.atomName leftSlot = leftTarget.name := by
    calc
      leftEnvironment.atomName leftSlot =
          (leftEnvironment.reifyOccurrence
            leftAlignment.sourceOccurrence).name :=
        (leftEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          leftAlignment.sourceOccurrence leftSlot leftSelected).symm
      _ = leftAlignment.reifiedOccurrence.name := by
        rw [leftAlignment.reified_eq]
      _ = leftTarget.name := leftAlignment.canonical_name_eq
  have rightAtomName : rightEnvironment.atomName rightSlot =
      rightTarget.name := by
    calc
      rightEnvironment.atomName rightSlot =
          (rightEnvironment.reifyOccurrence
            rightAtRoot.boundaryOccurrence).name :=
        (rightEnvironment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
          rightAtRoot.boundaryOccurrence rightSlot rightSelected).symm
      _ = (rightEnvironment.reifyOccurrence
            rightAlignment.sourceOccurrence).name := by rw [rightOccurrenceEq]
      _ = rightAlignment.reifiedOccurrence.name := by
        rw [rightAlignment.reified_eq]
      _ = rightTarget.name := rightAlignment.canonical_name_eq
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree rightAtRoot.certified.typed.boundary.targetSupport
      rightAtRoot.certified.typed.boundary.targetType (.fvar leftName) :=
    ⟨⟨WellSorted.HasType.fvar (by simpa [rightAtRoot] using leftLookup),
        rfl, rfl, rfl⟩,
      by
        intro presentation membership
        rfl⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree rightAtRoot.certified.typed.boundary.targetSupport
      rightAtRoot.certified.typed.boundary.targetType
      rightAtRoot.certified.typed.boundary.content :=
    ⟨⟨rightAtRoot.certified.typed.contentTyped,
        rightAtRoot.certified.typed.contentCanonicalBinderMetadata,
        rightAtRoot.certified.typed.contentObjectPattern,
        rightAtRoot.certified.typed.contentTyped.isWellScopedAt⟩,
      rightAtRoot.certified.typed.contentReflectiveScopeSafe⟩
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftWellSorted rightWellSorted
      (by simpa [rightAtRoot] using canonical)
      (by simpa [rightAtRoot] using smaller)
      (by simpa [rightAtRoot] using admissible))
  let selectedTree := rightAtRoot.selectedTreeFromForest rightEmbedding
    rightTrees
  have pairToSelected :
      (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (selectedTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel pair.rightTree selectedTree
      (by simpa [selectedTree, rightAtRoot] using
        rightAtRoot.certified.typed.contentObjectPattern)
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.alignment.normalize_pattern_eq
  have pairLeftNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .fvar leftName :=
    normalize_fvar_tree pair.leftTree
  have childNormal :
      (selectedTree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel).1 = .fvar leftName := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact pairToSelected.symm.trans (pairNormal.symm.trans pairLeftNormal)
  have rightAtom := rightAtRoot.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar leftName := by
    rw [leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      leftAlignment.sourceOccurrence leftSlot leftSelected, leftSourceOrigin]
    exact leftValues.assignment_sourceVariable leftName
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar leftName := by
    have normalEq := congrArg (fun atom => atom.key.normal) rightAtom
    have atomToChild : (rightEnvironment.atomValue rightSlot).key.normal =
        ((rightAtRoot.selectedTreeFromForest rightEmbedding rightTrees
          ).normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
    exact atomToChild.trans (by simpa only [selectedTree] using childNormal)
  let leaf :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        apexDeclaration depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot)))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
    apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
    apply PatternLeafAligned.leaf
    intro leafDepth
    apply leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
      rightEnvironment leftSlot rightSlot (leftNormal.trans rightNormal.symm)
    rw [leftNormal]
    rfl
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          leftEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
          (.fvar name)) leftAtomName)
    (congrArg
      (fun name =>
        (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
          rightEnvironment.lookupAtom?
          (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
          (.fvar name)) rightAtomName)
    leaf

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
