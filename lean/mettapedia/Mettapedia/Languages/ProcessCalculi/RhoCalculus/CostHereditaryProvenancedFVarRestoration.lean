import Mettapedia.GSLT.LanguageDef.CostRestorationSourceVariable
import Mettapedia.GSLT.LanguageDef.CostRestorationBoundaryVariable
import Mettapedia.GSLT.LanguageDef.CostStaticPlanProvenancedReification
import Mettapedia.GSLT.LanguageDef.CostStaticRootView
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostFillDeterminism
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical

/-!
# Restoration of membership-certified static free variables

The provenanced stop carrier exposes a rigid free-variable callback only when
the original name occurs in both static skeletons.  Such a name is either an
authored source variable or the collision-free name of a retained boundary.

The source-variable case is independent of recursive normalization.  In the
boundary case, equality of the encoded names identifies the same raw boundary,
and unambiguous static decomposition identifies the two independently built
child normal forms.  The resulting complete semantic-key equality places both
endpoint spellings in one slot of the common restoration cospan.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- Equal boundary names in two child-normalized forests carry equal compact
normal forms.  The proof retains the selected finite values on both sides and
uses unambiguous decomposition only after the collision-free name has
identified the common raw boundary. -/
theorem normalizedBoundaryResolved_normal_eq_of_name_eq
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    (name : String)
    (leftResolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
      color targetFree)
    (rightResolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
      color targetFree)
    (leftResolution :
      (leftTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve
        leftTable name = some leftResolved)
    (rightResolution :
      (rightTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve
        rightTable name = some rightResolved) :
    leftResolved.2.1 = rightResolved.2.1 := by
  have leftTableResolution : leftTable.resolve name = some leftResolved.1 := by
    have agrees :=
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve_boundary
          leftTable name
    rw [leftResolution] at agrees
    simpa using agrees.symm
  have rightTableResolution : rightTable.resolve name = some rightResolved.1 := by
    have agrees :=
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve_boundary
          rightTable name
    rw [rightResolution] at agrees
    simpa using agrees.symm
  have leftMembership : leftResolved.1 ∈ leftTable.entries :=
    leftTable.mem_entries_of_resolve_eq_some leftTableResolution
  have rightMembership : rightResolved.1 ∈ rightTable.entries :=
    rightTable.mem_entries_of_resolve_eq_some rightTableResolution
  obtain ⟨leftIndex, leftIndexEq⟩ := List.get_of_mem leftMembership
  obtain ⟨rightIndex, rightIndexEq⟩ := List.get_of_mem rightMembership
  have leftEntryBoundary : (leftTrees.getEntry leftIndex).boundary =
      leftResolved.1 :=
    (leftTrees.getEntry_boundary leftIndex).trans leftIndexEq
  have rightEntryBoundary : (rightTrees.getEntry rightIndex).boundary =
      rightResolved.1 :=
    (rightTrees.getEntry_boundary rightIndex).trans rightIndexEq
  obtain ⟨leftAtIndex, leftAtIndexResolution, _leftBoundary,
      leftAtIndexNormal⟩ :=
    leftTrees.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition leftIndex
  obtain ⟨rightAtIndex, rightAtIndexResolution, _rightBoundary,
      rightAtIndexNormal⟩ :=
    rightTrees.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition rightIndex
  have leftName : name =
      costRegionBoundaryVariableName leftResolved.1.boundary :=
    leftTable.name_eq_boundaryVariable_of_resolve_eq_some leftTableResolution
  have rightName : name =
      costRegionBoundaryVariableName rightResolved.1.boundary :=
    rightTable.name_eq_boundaryVariable_of_resolve_eq_some
      rightTableResolution
  have leftAtName :
      (leftTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve
        leftTable name = some leftAtIndex := by
    rw [leftName, ← leftEntryBoundary]
    exact leftAtIndexResolution
  have rightAtName :
      (rightTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).resolve
        rightTable name = some rightAtIndex := by
    rw [rightName, ← rightEntryBoundary]
    exact rightAtIndexResolution
  have leftResolvedEq : leftResolved = leftAtIndex := by
    exact Option.some.inj (leftResolution.symm.trans leftAtName)
  have rightResolvedEq : rightResolved = rightAtIndex := by
    exact Option.some.inj (rightResolution.symm.trans rightAtName)
  have rawBoundaryEq : leftResolved.1.boundary = rightResolved.1.boundary :=
    costRegionBoundaryVariableName_injective (leftName.symm.trans rightName)
  have typedBoundaryEq : leftResolved.1 = rightResolved.1 :=
    TypedCostRegionBoundary.ext rawBoundaryEq
  have entryBoundaryEq : (leftTrees.getEntry leftIndex).boundary =
      (rightTrees.getEntry rightIndex).boundary :=
    leftEntryBoundary.trans (typedBoundaryEq.trans rightEntryBoundary.symm)
  have treeNormalEq :
      ((leftTrees.getEntry leftIndex).tree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
      ((rightTrees.getEntry rightIndex).tree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 := by
    let rightReindexed :=
      (rightTrees.getEntry rightIndex).tree.reindexBoundary
        entryBoundaryEq.symm
    have aligned := CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel
      (leftTrees.getEntry leftIndex).tree rightReindexed
      (leftTrees.getEntry leftIndex).boundary.contentObjectPattern
    exact aligned.trans
      (CostRegionTree.reindexBoundary_normalizedBoundaryValue
        entryBoundaryEq.symm (rightTrees.getEntry rightIndex).tree)
  rw [leftResolvedEq, rightResolvedEq]
  exact leftAtIndexNormal.trans (treeNormalEq.trans rightAtIndexNormal.symm)

/-- A name occurring in both rho static skeletons has a common-restoration
apex after semantic-atom reification.  The source namespace uses the generic
authored-variable theorem; the boundary namespace uses collision-free raw
boundary identity plus rho's unambiguous child normalization. -/
noncomputable def memberFVar_commonRestorationApex
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
    (name : String)
    (leftMembership : name ∈ leftNode.skeleton.1.freeFvarNames)
    (rightMembership : name ∈ rightNode.skeleton.1.freeFvarNames)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.reifyName name)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.reifyName name))) := by
  obtain ⟨leftOccurrence, leftName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      leftMembership leftNode.skeleton.2.1.2.2.1
  obtain ⟨rightOccurrence, rightName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      rightMembership rightNode.skeleton.2.1.2.2.1
  obtain ⟨leftSlot, leftSelected⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have leftSelectedAtName : leftEnvironment.slotOfName? name = some leftSlot :=
    by simpa only [leftName] using leftSelected
  have rightSelectedAtName :
      rightEnvironment.slotOfName? name = some rightSlot :=
    by simpa only [rightName] using rightSelected
  have leftReifyName : leftEnvironment.reifyName name =
      leftEnvironment.atomName leftSlot := by
    simp only [CostStaticAtomEnvironment.reifyName, leftSelectedAtName]
  have rightReifyName : rightEnvironment.reifyName name =
      rightEnvironment.atomName rightSlot := by
    simp only [CostStaticAtomEnvironment.reifyName, rightSelectedAtName]
  cases decoded : decodeCostRegionSourceVariableName name with
  | some sourceName =>
      have encoded : name = costRegionSourceVariableName sourceName := by
        exact (decodeTaggedPayload_eq_some_iff
          costRegionSourceVariableTag name sourceName).mp decoded
      have leftOrigin : leftOccurrence.name =
          costRegionSourceVariableName sourceName := leftName.trans encoded
      have rightOrigin : rightOccurrence.name =
          costRegionSourceVariableName sourceName := rightName.trans encoded
      let apex := leftEnvironment.sourceVariable_commonRestorationApex
        rightEnvironment sourceName leftOccurrence rightOccurrence leftOrigin
          rightOrigin leftSlot rightSlot leftSelected rightSelected declaration
          depth
      exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
        (congrArg
          (fun atomName =>
            (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
              leftEnvironment.lookupAtom?
              (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
              (.fvar atomName)) leftReifyName.symm)
        (congrArg
          (fun atomName =>
            (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
              rightEnvironment.lookupAtom?
              (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
              (.fvar atomName)) rightReifyName.symm) apex
  | none =>
      let leftValues := leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      let rightValues := rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      have leftNotSource :
          decodeCostRegionSourceVariableName leftOccurrence.name = none := by
        simpa only [leftName] using decoded
      have rightNotSource :
          decodeCostRegionSourceVariableName rightOccurrence.name = none := by
        simpa only [rightName] using decoded
      obtain ⟨leftFreeType, leftLookup⟩ :=
        leftNode.skeleton.2.1.1.freeType_of_mem_freeFvarNames_of_isObjectPattern
          leftNode.skeleton.2.1.2.2.1
          leftOccurrence.name_mem_freeFvarNames
      obtain ⟨rightFreeType, rightLookup⟩ :=
        rightNode.skeleton.2.1.1.freeType_of_mem_freeFvarNames_of_isObjectPattern
          rightNode.skeleton.2.1.2.2.1
          rightOccurrence.name_mem_freeFvarNames
      have leftTableDefined :
          leftNode.boundaryTable.resolve leftOccurrence.name ≠ none := by
        intro unresolved
        simp [TypedCostRegionBoundaryTable.sourceFreeContext, leftNotSource]
          at leftLookup
        obtain ⟨boundary, resolution, _typeEq⟩ := leftLookup
        unfold CostStaticRegionNode.boundaryTable at unresolved
        rw [unresolved] at resolution
        cases resolution
      have rightTableDefined :
          rightNode.boundaryTable.resolve rightOccurrence.name ≠ none := by
        intro unresolved
        simp [TypedCostRegionBoundaryTable.sourceFreeContext, rightNotSource]
          at rightLookup
        obtain ⟨boundary, resolution, _typeEq⟩ := rightLookup
        unfold CostStaticRegionNode.boundaryTable at unresolved
        rw [unresolved] at resolution
        cases resolution
      have leftResolveSome :
          (leftValues.resolve leftNode.boundaryTable
            leftOccurrence.name).isSome = true := by
        cases valueResolution : leftValues.resolve leftNode.boundaryTable
            leftOccurrence.name with
        | none =>
            have agrees := leftValues.resolve_boundary leftNode.boundaryTable
              leftOccurrence.name
            rw [valueResolution] at agrees
            have tableUnresolved :
                leftNode.boundaryTable.resolve leftOccurrence.name = none := by
              simpa using agrees.symm
            exact (leftTableDefined tableUnresolved).elim
        | some value => rfl
      have rightResolveSome :
          (rightValues.resolve rightNode.boundaryTable
            rightOccurrence.name).isSome = true := by
        cases valueResolution : rightValues.resolve rightNode.boundaryTable
            rightOccurrence.name with
        | none =>
            have agrees := rightValues.resolve_boundary rightNode.boundaryTable
              rightOccurrence.name
            rw [valueResolution] at agrees
            have tableUnresolved :
                rightNode.boundaryTable.resolve rightOccurrence.name = none := by
              simpa using agrees.symm
            exact (rightTableDefined tableUnresolved).elim
        | some value => rfl
      obtain ⟨leftResolved, leftResolution⟩ :=
        Option.isSome_iff_exists.mp leftResolveSome
      obtain ⟨rightResolved, rightResolution⟩ :=
        Option.isSome_iff_exists.mp rightResolveSome
      have leftResolutionAtName : leftValues.resolve leftNode.boundaryTable
          name = some leftResolved := by
        simpa only [leftName] using leftResolution
      have rightResolutionAtName : rightValues.resolve rightNode.boundaryTable
          name = some rightResolved := by
        simpa only [rightName] using rightResolution
      have leftTableResolution : leftNode.boundaryTable.resolve name =
          some leftResolved.1 := by
        have agrees := leftValues.resolve_boundary leftNode.boundaryTable name
        rw [leftResolutionAtName] at agrees
        simpa using agrees.symm
      have rightTableResolution : rightNode.boundaryTable.resolve name =
          some rightResolved.1 := by
        have agrees := rightValues.resolve_boundary rightNode.boundaryTable name
        rw [rightResolutionAtName] at agrees
        simpa using agrees.symm
      have leftBoundaryName : name =
          costRegionBoundaryVariableName leftResolved.1.boundary :=
        leftNode.boundaryTable.name_eq_boundaryVariable_of_resolve_eq_some
          leftTableResolution
      have rightBoundaryName : name =
          costRegionBoundaryVariableName rightResolved.1.boundary :=
        rightNode.boundaryTable.name_eq_boundaryVariable_of_resolve_eq_some
          rightTableResolution
      have rawBoundaryEq : leftResolved.1.boundary =
          rightResolved.1.boundary :=
        costRegionBoundaryVariableName_injective
          (leftBoundaryName.symm.trans rightBoundaryName)
      have sameFiber : CostRegionBoundary.SameFiber
          leftResolved.1.boundary rightResolved.1.boundary :=
        ⟨congrArg CostRegionBoundary.type rawBoundaryEq,
          congrArg CostRegionBoundary.support rawBoundaryEq,
          congrArg CostRegionBoundary.targetType rawBoundaryEq,
          congrArg CostRegionBoundary.targetSupport rawBoundaryEq⟩
      have normalEq : leftResolved.2.1 = rightResolved.2.1 :=
        normalizedBoundaryResolved_normal_eq_of_name_eq leftTrees rightTrees
          name leftResolved rightResolved leftResolutionAtName
            rightResolutionAtName
      have keyEq := leftEnvironment.boundaryVariable_key_eq rightEnvironment
        leftOccurrence rightOccurrence leftSlot rightSlot leftSelected
          rightSelected leftNotSource rightNotSource leftResolved rightResolved
          leftResolution rightResolution sameFiber normalEq
      let apex := leftEnvironment.atomNames_commonRestorationApex_of_key_eq
        rightEnvironment leftSlot rightSlot keyEq declaration depth
      exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
        (congrArg
          (fun atomName =>
            (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
              leftEnvironment.lookupAtom?
              (leftEnvironment.semanticKeyCospan rightEnvironment).leftSlot
              (.fvar atomName)) leftReifyName.symm)
        (congrArg
          (fun atomName =>
            (leftEnvironment.semanticKeyCospan rightEnvironment).reifyWith
              rightEnvironment.lookupAtom?
              (leftEnvironment.semanticKeyCospan rightEnvironment).rightSlot
              (.fvar atomName)) rightReifyName.symm) apex

/-- A membership-certified rigid free-variable stop discharges the exact
depth-indexed semantic-leaf callback used by source-frame canonicalization.
The ordering keys are irrelevant at a free-variable root; all semantic content
comes from the uniform common-restoration apex above. -/
noncomputable def memberFVar_sourcePatternLeafAligned
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
    (name : String)
    (leftMembership : name ∈ leftNode.skeleton.1.freeFvarNames)
    (rightMembership : name ∈ rightNode.skeleton.1.freeFvarNames)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
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
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (.fvar (leftEnvironment.reifyName name)))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth (.fvar (rightEnvironment.reifyName name))) := by
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
  simp only [canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.reifyName name)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.reifyName name))) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
      (fun depth =>
        memberFVar_commonRestorationApex leftNode rightNode leftTrees
          rightTrees leftEnvironment rightEnvironment name leftMembership
            rightMembership rhoReflectivePresentation depth)
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars] using restores

/-- Rho source-frame alignment from a raw stop descent, with every rigid
free-variable callback discharged internally.  The caller is responsible
only for provenance-bearing plan stops; arbitrary or one-sided names are not
part of the interface. -/
noncomputable def reifiedSourceAlignment_of_rawAlignment
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
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    (rawDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    (planCallback : ∀ callbackAvailable callbackScope
      {leftAbstract rightAbstract},
      CostStaticPlanCanonicalStop leftNode.plan rightNode.plan
          rhoReflectivePresentation rawDeclaration rawStop leftAbstract
            rightAbstract →
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
          (canonicalizeByDepths leftKey rhoReflectivePresentation
            callbackAvailable callbackScope
            (leftEnvironment.reify leftAbstract))
          (canonicalizeByDepths rightKey rhoReflectivePresentation
            callbackAvailable callbackScope
            (rightEnvironment.reify rightAbstract))) :
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
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth (rightNode.reifiedSourceFrame rightEnvironment).1) := by
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
  apply leftNode.reifiedSourceProvenancedAlignment_of_rawAlignment
    rho_collectionChoiceDeterministic
    rhoReflectivePresentation rawDeclaration rightNode leftEnvironment
      rightEnvironment sameBound sameSort rawAligned leftKey rightKey
      availableDepth scopeDepth
  intro callbackAvailable callbackScope left right stopped
  cases stopped with
  | plan stop =>
      exact planCallback callbackAvailable callbackScope stop
  | sourceFVar name leftMembership rightMembership =>
      exact memberFVar_sourcePatternLeafAligned leftNode rightNode leftTrees
        rightTrees leftEnvironment rightEnvironment name leftMembership
          rightMembership leftKey rightKey callbackAvailable callbackScope

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
