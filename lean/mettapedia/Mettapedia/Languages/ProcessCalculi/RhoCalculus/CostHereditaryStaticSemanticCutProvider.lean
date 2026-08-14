import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticSemanticCut
import Mettapedia.GSLT.LanguageDef.CostStaticPlanSelection

/-!
# Constructive rho semantic-cut provider cases

The generic canonical-pair recursion returns a completed child elaboration.
At a stopped rho Quote/Drop boundary this is sufficient, but the parent
occurrence must be replayed before the child certificate is forgotten.  This
module performs that replay and returns the enclosing semantic exposure
itself.  The final paired elaboration is therefore obtained only by the
semantic-cut eliminator.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

/-- Invert one occurrence selected in a common-reified target frame back to
the exact reached or stopped view of the static plan that produced it.

The preimage is intentionally existential.  Semantic-atom environments and
common-key cospans may identify distinct source names, so neither the raw
payload nor its source zipper is unique.  The returned inventory view keeps
one actual preimage, its exact boundary-table embedding, and the complete
transport equations through presentation mapping, ambient-binder insertion,
environment reification, and the chosen common-cospan leg. -/
theorem exists_planContextInventoryView_of_commonOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (occurrence : CostStaticFVarOccurrence
      (cospan.reifyWith environment.lookupAtom? leg
        (node.reifyTargetFrame environment))) :
    ∃ rawPayload,
      ∃ view : CostStaticPlanContextInventoryView source color targetFree
        rawPayload node.plan.abstractPattern node.plan.boundaryTable.entries,
      let mapped := ContextSubstitution.renameAmbientContextAt
        node.thinning.toTargetIndex 0
        (CIGSLT.mapOneHoleContext (color.symbols source)
          view.view.abstractContext)
      cospan.reifyEnvironmentContext environment leg mapped.1 =
          occurrence.context ∧
        cospan.reifyWith environment.lookupAtom? leg
          (environment.reify
            (node.thinning.thickenAmbientBVars mapped.2
              (mapPattern (color.symbols source)
                view.view.selectedAbstract))) =
          .fvar occurrence.name := by
  obtain ⟨cospanPayload, cospanContext, cospanSelected,
      cospanContextEquality, cospanPayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_cospanReifyWith
      cospan environment.lookupAtom? leg occurrence.selected
  have environmentSelected :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.Selects
        cospanPayload cospanContext
      (environment.reify node.mappedThickenedSkeleton.1) := by
    simpa only [CostStaticRegionNode.reifyTargetFrame] using cospanSelected
  obtain ⟨environmentPayload, environmentContext, sourceSelected,
      environmentContextEquality, environmentPayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_environmentReify
      environment environmentSelected
  rw [node.mappedThickenedSkeleton_pattern] at sourceSelected
  obtain ⟨mappedPayload, mappedContext, holeDepth, mappedSelected,
      mappedContextEquality, mappedPayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_thickenAmbientBVars
      node.thinning 0 sourceSelected
  obtain ⟨sourcePayload, sourceContext, planSelected,
      sourceContextEquality, sourcePayloadEquality⟩ :=
    Mettapedia.GSLT.LanguageDef.Selects.exists_preimage_mapPattern
      (color.symbols source) mappedSelected
  have planSelected' :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.Selects
        sourcePayload sourceContext
      node.plan.abstractPattern := by
    rw [← node.skeleton_pattern]
    exact planSelected
  obtain ⟨rawPayload, view, viewContextEquality, viewPayloadEquality⟩ :=
    node.plan.exists_contextInventoryView_of_abstractSelection planSelected'
  refine ⟨rawPayload, view, ?_⟩
  dsimp only
  constructor
  · rw [viewContextEquality, sourceContextEquality, mappedContextEquality]
    exact (congrArg
      (cospan.reifyContextWith environment.lookupAtom? leg)
      environmentContextEquality).trans cospanContextEquality
  · rw [viewContextEquality, sourceContextEquality, mappedContextEquality,
      viewPayloadEquality, sourcePayloadEquality, mappedPayloadEquality,
      environmentPayloadEquality, cospanPayloadEquality]

end CostStaticRegionNode

namespace RhoCollapsingLeafExposure

/-- Replay an exact stopped Quote/Drop occurrence before eliminating the
strictly smaller child pair.

The child elaborator may choose either endpoint tree.  The chosen right tree
is transported into the parent fibre and compared with the caller's actual
right tree using static-decomposition unambiguity.  The result retains the
parent node, its finite child forest, and the selected semantic slot in a
`RhoCollapsingLeafExposure`; it does not package the final pair alignment. -/
noncomputable def stoppedQuoteDropOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCollapsingLeafExposure leftView.node leftView.children right := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType rightPattern := by
    simpa only [boundarySupport, boundaryType] using rightWellSorted
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content + sizeOf rightPattern <
        sizeOf leftPattern + sizeOf rightPattern := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  let ambientRight : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type :=
    ((childPair.rightTree.extendOuter outer).reindexAvailable boundarySupport
      ).reindexType boundaryType
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have typeReindex := CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundaryType
      ((childPair.rightTree.extendOuter outer).reindexAvailable
        boundarySupport)
    have supportReindex := CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundarySupport
      (childPair.rightTree.extendOuter outer)
    have weakened := childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer
    exact (typeReindex.trans (supportReindex.trans weakened)).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightWellSorted.1.2.2.1
  exact stoppedQuoteDropBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding shell
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))

/-- Singleton-parallel counterpart of `stoppedQuoteDropOfCloseSmaller`.

The recursive child is selected and closed before the bare parallel shell is
collapsed.  Returning the exposure, instead of its already-erased pair
elaboration, keeps the exact stopped occurrence available to the enclosing
semantic-cut case. -/
noncomputable def stoppedParallelSingletonOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCollapsingLeafExposure leftView.node leftView.children right := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType rightPattern := by
    simpa only [boundarySupport, boundaryType] using rightWellSorted
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content + sizeOf rightPattern <
        sizeOf leftPattern + sizeOf rightPattern := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  let ambientRight : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type :=
    ((childPair.rightTree.extendOuter outer).reindexAvailable boundarySupport
      ).reindexType boundaryType
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have typeReindex := CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundaryType
      ((childPair.rightTree.extendOuter outer).reindexAvailable
        boundarySupport)
    have supportReindex := CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundarySupport
      (childPair.rightTree.extendOuter outer)
    have weakened := childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer
    exact (typeReindex.trans (supportReindex.trans weakened)).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightWellSorted.1.2.2.1
  exact stoppedParallelSingletonBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding shell
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))

end RhoCollapsingLeafExposure

namespace RhoCanonicalStaticPairSemanticCut

/-- The stopped left Quote/Drop provider case, retaining the enclosing
occurrence exposure until the semantic-cut eliminator. -/
noncomputable def leftStoppedQuoteDropOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut color left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedQuoteDropOfCloseSmaller left right
      leftView rightWellSorted state entryEmbedding shell boundaryCanonical
      boundarySupport boundaryType closeSmaller)

/-- The right-oriented stopped Quote/Drop provider case is obtained by
replaying the exact right occurrence and reversing only at the semantic-cut
boundary. -/
noncomputable def rightStoppedQuoteDropOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rightView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] rightView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .apply rhoReflectivePresentation.quoteConstructor []
        (.apply rhoReflectivePresentation.dropConstructor [] .hole []) [])
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          leftPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut color left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedQuoteDropOfCloseSmaller right left
      rightView leftWellSorted state entryEmbedding shell boundaryCanonical
      boundarySupport boundaryType (fun {childAvailable childOuter childLeft
        childRight childType} leftChildWellSorted rightChildWellSorted
        canonical smaller admissible => by
          let paired := Classical.choice
            (closeSmaller (childAvailable := childAvailable)
              (childOuter := childOuter) (leftChild := childRight)
              (rightChild := childLeft) (childType := childType)
              rightChildWellSorted leftChildWellSorted canonical.symm
              (by simpa [Nat.add_comm] using smaller) admissible)
          exact ⟨paired.symm⟩))

/-- The stopped left singleton-parallel provider case. -/
noncomputable def leftStoppedParallelSingletonOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut color left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedParallelSingletonOfCloseSmaller
      left right leftView rightWellSorted state entryEmbedding shell
      boundaryCanonical boundarySupport boundaryType closeSmaller)

/-- The stopped right singleton-parallel provider case. -/
noncomputable def rightStoppedParallelSingletonOfCloseSmaller
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rightView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] rightView.node.finiteBoundaryTable.entries)
    (shell : state.skeletonContext =
      .collection rhoReflectivePresentation.parallelCollection
        [] .hole [] none)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          leftPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut color left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedParallelSingletonOfCloseSmaller
      right left rightView leftWellSorted state entryEmbedding shell
      boundaryCanonical boundarySupport boundaryType
        (fun {childAvailable childOuter childLeft childRight childType}
          leftChildWellSorted rightChildWellSorted canonical smaller
          admissible => by
            let paired := Classical.choice
              (closeSmaller (childAvailable := childAvailable)
                (childOuter := childOuter) (leftChild := childRight)
                (rightChild := childLeft) (childType := childType)
                rightChildWellSorted leftChildWellSorted canonical.symm
                (by simpa [Nat.add_comm] using smaller) admissible)
            exact ⟨paired.symm⟩))

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
