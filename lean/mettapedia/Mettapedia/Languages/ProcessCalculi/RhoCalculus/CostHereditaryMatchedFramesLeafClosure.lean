import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesAvailableLeaf

/-!
# Recursive closure of matched rho boundary leaves

The paired plan traversal supplies canonical equality, strict descent, and
admissibility for two selected boundary contents.  This module performs the
remaining local work: it chooses the common active support, transports a
sealed endpoint into that support, invokes the well-founded child closure,
and lifts the resulting semantic atom apex through the exact stopped plan
contexts.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticPlanStopped

/-- Close two selected stopped boundaries directly at their semantic atoms.

This is the local leaf form of the recursive closure theorem.  It derives the
common active support, recursively closes the two selected child contents, and
returns only the semantic atom apex.  Structural callers can compose that leaf
without first rebuilding either complete plan context. -/
noncomputable def selectedAtoms_commonRestorationApex_of_closeSmaller
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
    (supportCase :
      left.certified.typed.boundary.targetSupport =
          right.certified.typed.boundary.targetSupport ∨
      left.certified.typed.boundary.targetSupport = [] ∨
      right.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (childDeclaration apexDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration left.certified.typed.boundary.content =
        canonicalize childDeclaration right.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf left.certified.typed.boundary.content +
          sizeOf right.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      right.certified.typed.boundary.targetType)
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
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree left.certified.typed.boundary.targetSupport
      left.certified.typed.boundary.targetType
      left.certified.typed.boundary.content :=
    ⟨⟨left.certified.typed.contentTyped,
        left.certified.typed.contentCanonicalBinderMetadata,
        left.certified.typed.contentObjectPattern,
        left.certified.typed.contentTyped.isWellScopedAt⟩,
      left.certified.typed.contentReflectiveScopeSafe⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree right.certified.typed.boundary.targetSupport
      right.certified.typed.boundary.targetType
      right.certified.typed.boundary.content :=
    ⟨⟨right.certified.typed.contentTyped,
        right.certified.typed.contentCanonicalBinderMetadata,
        right.certified.typed.contentObjectPattern,
        right.certified.typed.contentTyped.isWellScopedAt⟩,
      right.certified.typed.contentReflectiveScopeSafe⟩
  rcases supportCase with supportEq | leftSealed | rightSealed
  · have leftAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree right.certified.typed.boundary.targetSupport
        right.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [supportEq, typeEq] using leftWellSorted
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAtCommon rightWellSorted canonical
        smaller rightAdmissible)
    exact selectedEnvironmentAtoms_commonRestorationApex_of_sameSupportPair
      left right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected supportEq typeEq pair apexDeclaration depth
  · have leftClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] left.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [leftSealed] using leftWellSorted
    have leftAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree right.certified.typed.boundary.targetSupport
        right.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [typeEq] using
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          leftClosed right.certified.typed.boundary.targetSupport
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAtCommon rightWellSorted canonical
        smaller rightAdmissible)
    exact selectedEnvironmentAtoms_commonRestorationApex_of_leftSealedPair
      left right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected leftSealed typeEq pair apexDeclaration depth
  · have rightClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] right.certified.typed.boundary.targetType
        right.certified.typed.boundary.content := by
      simpa only [rightSealed] using rightWellSorted
    have rightAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree left.certified.typed.boundary.targetSupport
        left.certified.typed.boundary.targetType
        right.certified.typed.boundary.content := by
      have widened :=
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          rightClosed left.certified.typed.boundary.targetSupport
      simpa only [typeEq] using widened
    have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
        left.certified.typed.boundary.targetType := by
      simpa only [typeEq] using rightAdmissible
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftWellSorted rightAtCommon canonical
        smaller leftAdmissible)
    exact selectedEnvironmentAtoms_commonRestorationApex_of_rightSealedPair
      left right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected rightSealed typeEq pair apexDeclaration depth

/-- Close two selected stopped boundaries under the three support regimes
forced by positional rho availability: equal support, sealed left, or sealed
right.

The child closure uses the declaration that classified the original pair.
The returned restoration apex uses the intrinsic declaration of the two
same-colour static frames; these declarations need not be definitionally the
same in an enclosing bridge case. -/
noncomputable def selectedRoots_commonRestorationApex_of_closeSmaller
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
    (supportCase :
      left.certified.typed.boundary.targetSupport =
          right.certified.typed.boundary.targetSupport ∨
      left.certified.typed.boundary.targetSupport = [] ∨
      right.certified.typed.boundary.targetSupport = [])
    (typeEq : left.certified.typed.boundary.targetType =
      right.certified.typed.boundary.targetType)
    (childDeclaration apexDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration left.certified.typed.boundary.content =
        canonicalize childDeclaration right.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf left.certified.typed.boundary.content +
          sizeOf right.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      right.certified.typed.boundary.targetType)
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
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan apexDeclaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      apexDeclaration depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree left.certified.typed.boundary.targetSupport
      left.certified.typed.boundary.targetType
      left.certified.typed.boundary.content :=
    ⟨⟨left.certified.typed.contentTyped,
        left.certified.typed.contentCanonicalBinderMetadata,
        left.certified.typed.contentObjectPattern,
        left.certified.typed.contentTyped.isWellScopedAt⟩,
      left.certified.typed.contentReflectiveScopeSafe⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree right.certified.typed.boundary.targetSupport
      right.certified.typed.boundary.targetType
      right.certified.typed.boundary.content :=
    ⟨⟨right.certified.typed.contentTyped,
        right.certified.typed.contentCanonicalBinderMetadata,
        right.certified.typed.contentObjectPattern,
        right.certified.typed.contentTyped.isWellScopedAt⟩,
      right.certified.typed.contentReflectiveScopeSafe⟩
  rcases supportCase with supportEq | leftSealed | rightSealed
  · have leftAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree right.certified.typed.boundary.targetSupport
        right.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [supportEq, typeEq] using leftWellSorted
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAtCommon rightWellSorted canonical
        smaller rightAdmissible)
    exact selectedRoots_commonRestorationApex_of_sameSupportPair left right
      leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
        rightEnvironment leftSlot leftSelected rightSlot rightSelected
        supportEq typeEq pair apexDeclaration depth holeDepth contexts
  · have leftClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] left.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [leftSealed] using leftWellSorted
    have leftAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree right.certified.typed.boundary.targetSupport
        right.certified.typed.boundary.targetType
        left.certified.typed.boundary.content := by
      simpa only [typeEq] using
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          leftClosed right.certified.typed.boundary.targetSupport
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAtCommon rightWellSorted canonical
        smaller rightAdmissible)
    exact selectedRoots_commonRestorationApex_of_leftSealedPair left right
      leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
        rightEnvironment leftSlot leftSelected rightSlot rightSelected
        leftSealed typeEq pair apexDeclaration depth holeDepth contexts
  · have rightClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] right.certified.typed.boundary.targetType
        right.certified.typed.boundary.content := by
      simpa only [rightSealed] using rightWellSorted
    have rightAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree left.certified.typed.boundary.targetSupport
        left.certified.typed.boundary.targetType
        right.certified.typed.boundary.content := by
      have widened :=
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          rightClosed left.certified.typed.boundary.targetSupport
      simpa only [typeEq] using widened
    have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
        left.certified.typed.boundary.targetType := by
      simpa only [typeEq] using rightAdmissible
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftWellSorted rightAtCommon canonical
        smaller leftAdmissible)
    exact selectedRoots_commonRestorationApex_of_rightSealedPair left right
      leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
        rightEnvironment leftSlot leftSelected rightSlot rightSelected
        rightSealed typeEq pair apexDeclaration depth holeDepth contexts

end CostStaticPlanStopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
