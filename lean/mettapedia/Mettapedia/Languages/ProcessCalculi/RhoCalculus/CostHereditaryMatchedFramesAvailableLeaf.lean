import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryTreeAvailabilityTransposition
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesApex

/-!
# Availability transport for matched rho boundary leaves

A paired elaboration compares both endpoints at one active availability.  A
selected boundary leaf, however, may have been retained in the sealed regime
with empty support.  The hereditary availability-suffix theorem moves that
sealed endpoint into the pair's active availability.  Paired normalization
then crosses to the other endpoint, and structural unambiguity identifies the
pair's retained endpoint with the exact selected tree.

This bridge compares normalized boundary values only.  It does not identify
their complete semantic-atom keys or their common-frame names.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace RhoMatchedBoundaryLeaf

/-- A rho canonical pair at the exposed availability identifies the exact
normalized value of a sealed left endpoint with the exact normalized value of
an exposed right endpoint. -/
theorem normalize_pattern_eq_of_leftSealed_pair
    {targetFree : WellSorted.FreeTypeContext}
    {available : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree [] [] leftPattern type)
    (right : CostRegionTree rhoCIGSLT targetFree available [] rightPattern
      type)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available [] leftPattern
        rightPattern type) :
    (left.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  have leftToPair :
      (left.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
      (smallAvailable := []) (largeAvailable := available)
        (ambient := available) (by simp) left pair.leftTree rfl rfl leftObject
  have pairEq :
      (pair.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.normalize_pattern_eq
  have pairToRight :
      (pair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    Mettapedia.GSLT.LanguageDef.CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
        rhoHereditaryNormalizationKernel pair.rightTree right rightObject
  exact leftToPair.trans (pairEq.trans pairToRight)

/-- Symmetric sealed-right form of
`normalize_pattern_eq_of_leftSealed_pair`. -/
theorem normalize_pattern_eq_of_rightSealed_pair
    {targetFree : WellSorted.FreeTypeContext}
    {available : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available [] leftPattern type)
    (right : CostRegionTree rhoCIGSLT targetFree [] [] rightPattern type)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available [] leftPattern
        rightPattern type) :
    (left.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact (normalize_pattern_eq_of_leftSealed_pair right left rightObject
    leftObject pair.symm).symm

/-- Index-tolerant form of `normalize_pattern_eq_of_leftSealed_pair`.

The selected boundary trees retain their independently certified supports
and result types.  The equalities transport only those dependent indices;
normalization is unchanged by either transport. -/
theorem normalize_pattern_eq_of_leftSealed_pair_reindexed
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftPattern rightPattern : Pattern}
    {leftType rightType : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree leftAvailable [] leftPattern
      leftType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable []
      rightPattern rightType)
    (leftSealed : leftAvailable = [])
    (typeEq : leftType = rightType)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree rightAvailable []
        leftPattern rightPattern rightType) :
    (left.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  let movedAvailable := left.reindexAvailable leftSealed
  let moved := movedAvailable.reindexType typeEq
  have availableTransport :
      (movedAvailable.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (left.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.reindexAvailable_normalize
      rhoHereditaryStaticNormalizer leftSealed left
  have typeTransport :
      (moved.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (movedAvailable.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.reindexType_normalize rhoHereditaryStaticNormalizer
      typeEq movedAvailable
  exact availableTransport.symm.trans (typeTransport.symm.trans
    (normalize_pattern_eq_of_leftSealed_pair moved right leftObject
      rightObject pair))

/-- Symmetric index-tolerant sealed-right form. -/
theorem normalize_pattern_eq_of_rightSealed_pair_reindexed
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftPattern rightPattern : Pattern}
    {leftType rightType : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree leftAvailable [] leftPattern
      leftType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable []
      rightPattern rightType)
    (rightSealed : rightAvailable = [])
    (typeEq : leftType = rightType)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftAvailable [] leftPattern
        rightPattern leftType) :
    (left.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact (normalize_pattern_eq_of_leftSealed_pair_reindexed right left
    rightSealed typeEq.symm rightObject leftObject pair.symm).symm

/-- A canonical pair also identifies independently elaborated endpoints when
their retained active contexts agree.  The two endpoint trees may carry
propositionally equal context and result-type indices; reindexing changes no
computed normal form. -/
theorem normalize_pattern_eq_of_sameAvailable_pair_reindexed
    {targetFree : WellSorted.FreeTypeContext}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftPattern rightPattern : Pattern}
    {leftType rightType : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree leftAvailable [] leftPattern
      leftType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable []
      rightPattern rightType)
    (availableEq : leftAvailable = rightAvailable)
    (typeEq : leftType = rightType)
    (leftObject : WellSorted.isObjectPattern leftPattern = true)
    (rightObject : WellSorted.isObjectPattern rightPattern = true)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree rightAvailable []
        leftPattern rightPattern rightType) :
    (left.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  let movedAvailable := left.reindexAvailable availableEq
  let moved := movedAvailable.reindexType typeEq
  have availableTransport :
      (movedAvailable.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (left.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.reindexAvailable_normalize
      rhoHereditaryStaticNormalizer availableEq left
  have typeTransport :
      (moved.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (movedAvailable.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.reindexType_normalize rhoHereditaryStaticNormalizer
      typeEq movedAvailable
  have leftToPair :
      (moved.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
        rhoHereditaryNormalizationKernel moved pair.leftTree leftObject
  have pairEq :
      (pair.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      pair.normalize_pattern_eq
  have pairToRight :
      (pair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
        rhoHereditaryNormalizationKernel pair.rightTree right rightObject
  exact availableTransport.symm.trans (typeTransport.symm.trans
    (leftToPair.trans (pairEq.trans pairToRight)))

end RhoMatchedBoundaryLeaf

namespace CostStaticPlanStopped

/-- The exact children selected by two stopped plan traversals have equal rho
normal values when the left boundary is sealed and the well-founded child
closure supplies a pair at the right boundary's exposed availability.

The keep/skip embeddings choose positions before any equality is used, so
duplicate boundary spellings remain distinct. -/
theorem selectedTree_normalize_pattern_eq_of_leftSealed_pair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    (leftSealed : left.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType) :
    ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact RhoMatchedBoundaryLeaf.normalize_pattern_eq_of_leftSealed_pair_reindexed
    (left.selectedTreeFromForest leftEmbedding leftTrees)
    (right.selectedTreeFromForest rightEmbedding rightTrees) leftSealed typeEq
    left.certified.typed.contentObjectPattern
    right.certified.typed.contentObjectPattern pair

/-- Symmetric stopped-plan companion with a sealed right boundary. -/
theorem selectedTree_normalize_pattern_eq_of_rightSealed_pair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    (rightSealed : right.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        left.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        left.certified.typed.boundary.targetType) :
    ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact RhoMatchedBoundaryLeaf.normalize_pattern_eq_of_rightSealed_pair_reindexed
    (left.selectedTreeFromForest leftEmbedding leftTrees)
    (right.selectedTreeFromForest rightEmbedding rightTrees) rightSealed typeEq
    left.certified.typed.contentObjectPattern
    right.certified.typed.contentObjectPattern pair

/-- The exact children selected by two stopped traversals have equal normal
values when their retained supports agree and the child closure supplies a
canonical pair at that common support. -/
theorem selectedTree_normalize_pattern_eq_of_sameSupport_pair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    (supportEq : left.certified.typed.boundary.targetSupport =
      right.certified.typed.boundary.targetSupport)
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType) :
    ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact
    RhoMatchedBoundaryLeaf.normalize_pattern_eq_of_sameAvailable_pair_reindexed
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees) supportEq typeEq
      left.certified.typed.contentObjectPattern
      right.certified.typed.contentObjectPattern pair

/-- A sealed/exposed child pair constructs the actual semantic restoration
leaf selected in the two parent environments.  Equality of normalized values
is derived from the pair; sealedness of the semantic atom is derived from the
same positional boundary replay. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_leftSealedPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (leftSealed : left.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have normalEq := selectedTree_normalize_pattern_eq_of_leftSealed_pair
    left right leftEmbedding rightEmbedding leftTrees rightTrees leftSealed
      typeEq pair
  have leftAtom := left.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have environmentSealed :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] := by
    have supportEq := congrArg (fun atom => atom.key.targetSupport) leftAtom
    simpa only [TypedCostStaticAtom.ofBoundaryValue, leftSealed] using supportEq
  exact selectedEnvironmentAtoms_commonRestorationApex_of_normalEq left right
    leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
      rightEnvironment leftSlot leftSelected rightSlot rightSelected
      (by simpa only [rhoHereditaryNormalizationKernel] using normalEq)
      environmentSealed declaration depth

/-- Right-sealed semantic-leaf companion. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_rightSealedPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (rightSealed : right.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        left.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        left.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have normalEq := selectedTree_normalize_pattern_eq_of_rightSealed_pair
    left right leftEmbedding rightEmbedding leftTrees rightTrees rightSealed
      typeEq pair
  have rightAtom := right.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have environmentSealed :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [] := by
    have supportEq := congrArg (fun atom => atom.key.targetSupport) rightAtom
    simpa only [TypedCostStaticAtom.ofBoundaryValue, rightSealed] using supportEq
  exact selectedEnvironmentAtoms_commonRestorationApex_of_rightNormalEq
    left right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected
      (by simpa only [rhoHereditaryNormalizationKernel] using normalEq)
      environmentSealed declaration depth

/-- Equal-support child pairs construct the selected semantic restoration
leaf without a sealedness premise.  The pair supplies normal equality and the
stopped boundary witnesses supply equality of the support component observed
by restoration. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_sameSupportPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.certified.typed.boundary.targetSupport =
      right.certified.typed.boundary.targetSupport)
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have normalEq := selectedTree_normalize_pattern_eq_of_sameSupport_pair
    left right leftEmbedding rightEmbedding leftTrees rightTrees supportEq
      typeEq pair
  exact
    selectedEnvironmentAtoms_commonRestorationApex_of_sameSupportNormalEq
      left right leftEmbedding rightEmbedding leftTrees rightTrees
        leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
        rightSelected
        (by simpa only [rhoHereditaryNormalizationKernel] using normalEq)
        supportEq declaration depth

/-- Lift an equal-support child pair through the exact stopped plan contexts
to the complete parent abstract roots. -/
noncomputable def selectedRoots_commonRestorationApex_of_sameSupportPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.certified.typed.boundary.targetSupport =
      right.certified.typed.boundary.targetSupport)
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let atomApex :=
    selectedEnvironmentAtoms_commonRestorationApex_of_sameSupportPair
      left right leftEmbedding rightEmbedding leftTrees rightTrees
        leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
        rightSelected supportEq typeEq pair declaration holeDepth
  exact selectedRoots_commonRestorationApex_of_atomApex left right
    leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected declaration depth holeDepth atomApex contexts

/-- Lift a left-sealed child pair through the two exact stopped plan contexts
to the complete parent abstract roots.  The only remaining input is the rigid
context alignment; all selected-leaf semantics come from the child pair and
the replayed boundary positions. -/
noncomputable def selectedRoots_commonRestorationApex_of_leftSealedPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (leftSealed : left.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        right.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        right.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  have normalEq := selectedTree_normalize_pattern_eq_of_leftSealed_pair
    left right leftEmbedding rightEmbedding leftTrees rightTrees leftSealed
      typeEq pair
  have leftAtom := left.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have environmentSealed :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] := by
    have supportEq := congrArg (fun atom => atom.key.targetSupport) leftAtom
    simpa only [TypedCostStaticAtom.ofBoundaryValue, leftSealed] using supportEq
  exact selectedRoots_commonRestorationApex_of_normalEq left right
    leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
      rightEnvironment leftSlot leftSelected rightSlot rightSelected
      (by simpa only [rhoHereditaryNormalizationKernel] using normalEq)
      (Or.inl environmentSealed) declaration depth holeDepth contexts

/-- Right-sealed companion of
`selectedRoots_commonRestorationApex_of_leftSealedPair`. -/
noncomputable def selectedRoots_commonRestorationApex_of_rightSealedPair
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (rightSealed : right.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree
        left.certified.typed.boundary.targetSupport []
        left.certified.typed.boundary.content
        right.certified.typed.boundary.content
        left.certified.typed.boundary.targetType)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  have normalEq := selectedTree_normalize_pattern_eq_of_rightSealed_pair
    left right leftEmbedding rightEmbedding leftTrees rightTrees rightSealed
      typeEq pair
  have rightAtom := right.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have environmentSealed :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [] := by
    have supportEq := congrArg (fun atom => atom.key.targetSupport) rightAtom
    simpa only [TypedCostStaticAtom.ofBoundaryValue, rightSealed] using supportEq
  exact selectedRoots_commonRestorationApex_of_normalEq left right
    leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
      rightEnvironment leftSlot leftSelected rightSlot rightSelected
      (by simpa only [rhoHereditaryNormalizationKernel] using normalEq)
      (Or.inr environmentSealed) declaration depth holeDepth contexts

end CostStaticPlanStopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
