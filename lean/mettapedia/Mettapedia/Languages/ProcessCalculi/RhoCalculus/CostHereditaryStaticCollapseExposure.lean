import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticDeepAtomExposure
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnosticDepths

/-!
# Collapsing-context exposure for hereditary rho Cost

A stopped static-plan occurrence need not lie under a member of a chosen
syntactic shell grammar.  The intrinsic criterion is instead semantic: after
placing a fresh variable at the occurrence, ordinary reflective
canonicalization returns exactly that variable.  The generic collapse theorem
then proves that the fixed context contains no free variables and evaporates
for every filler.  Order-agnosticity transfers the result to the keyed
two-depth canonicalizer used by hereditary normalization.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticAtomEnvironment

/-- Reification fixes a pattern which contains no free variables. -/
theorem reify_eq_self_of_freeFvarNames_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ pattern : Pattern, pattern.freeFvarNames = [] →
      environment.reify pattern = pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _
      simp [CostStaticAtomEnvironment.reify]
  | hfvar name =>
      intro noFree
      simp [Pattern.freeFvarNames] at noFree
  | happly constructor arguments inductionHypothesis =>
      intro noFree
      simp only [Pattern.freeFvarNames, List.flatMap_eq_nil_iff] at noFree
      simp only [CostStaticAtomEnvironment.reify, Pattern.apply.injEq, true_and]
      exact (List.map_congr_left fun argument membership =>
          inductionHypothesis argument membership
            (noFree argument membership)).trans (by simp)
  | hlambda binder body inductionHypothesis =>
      intro noFree
      simp only [Pattern.freeFvarNames] at noFree
      simp [CostStaticAtomEnvironment.reify, inductionHypothesis noFree]
  | hmultiLambda arity binders body inductionHypothesis =>
      intro noFree
      simp only [Pattern.freeFvarNames] at noFree
      simp [CostStaticAtomEnvironment.reify, inductionHypothesis noFree]
  | hsubst body replacement bodyInduction replacementInduction =>
      intro noFree
      simp only [Pattern.freeFvarNames, List.append_eq_nil_iff] at noFree
      simp [CostStaticAtomEnvironment.reify, bodyInduction noFree.1,
        replacementInduction noFree.2]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro noFree
      simp only [Pattern.freeFvarNames, List.append_eq_nil_iff,
        List.flatMap_eq_nil_iff] at noFree
      simp only [CostStaticAtomEnvironment.reify, Pattern.collection.injEq,
        true_and, and_true]
      exact (List.map_congr_left fun element membership =>
          inductionHypothesis element membership
            (noFree.1 element membership)).trans (by simp)

/-- Reification fixes the complete frame of a one-hole context when that
frame contains no free variables. -/
theorem reifyContext_eq_self_of_frameFreeFvarNames_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ context : OneHoleContext, contextFrameFreeFvarNames context = [] →
      environment.reifyContext context = context := by
  intro context
  induction context with
  | hole =>
      intro _
      rfl
  | apply constructor before inner after inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames, List.append_eq_nil_iff,
        List.flatMap_eq_nil_iff] at noFree
      simp only [CostStaticAtomEnvironment.reifyContext,
        OneHoleContext.apply.injEq, true_and]
      refine ⟨?_, inductionHypothesis noFree.1.2, ?_⟩
      · exact (List.map_congr_left fun pattern membership =>
          reify_eq_self_of_freeFvarNames_eq_nil environment pattern
            (noFree.1.1 pattern membership)).trans (by simp)
      · exact (List.map_congr_left fun pattern membership =>
          reify_eq_self_of_freeFvarNames_eq_nil environment pattern
            (noFree.2 pattern membership)).trans (by simp)
  | lambda binder inner inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames] at noFree
      simp [CostStaticAtomEnvironment.reifyContext,
        inductionHypothesis noFree]
  | multiLambda arity binders inner inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames] at noFree
      simp [CostStaticAtomEnvironment.reifyContext,
        inductionHypothesis noFree]
  | substBody inner replacement inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames, List.append_eq_nil_iff] at noFree
      simp [CostStaticAtomEnvironment.reifyContext,
        inductionHypothesis noFree.1,
        reify_eq_self_of_freeFvarNames_eq_nil environment replacement
          noFree.2]
  | substReplacement body inner inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames, List.append_eq_nil_iff] at noFree
      simp [CostStaticAtomEnvironment.reifyContext,
        reify_eq_self_of_freeFvarNames_eq_nil environment body noFree.1,
        inductionHypothesis noFree.2]
  | collection collectionType before inner after rest inductionHypothesis =>
      intro noFree
      simp only [contextFrameFreeFvarNames, List.append_eq_nil_iff,
        List.flatMap_eq_nil_iff] at noFree
      simp only [CostStaticAtomEnvironment.reifyContext,
        OneHoleContext.collection.injEq, true_and, and_true]
      refine ⟨?_, inductionHypothesis noFree.1.1.2, ?_⟩
      · exact (List.map_congr_left fun pattern membership =>
          reify_eq_self_of_freeFvarNames_eq_nil environment pattern
            (noFree.1.1.1 pattern membership)).trans (by simp)
      · exact (List.map_congr_left fun pattern membership =>
          reify_eq_self_of_freeFvarNames_eq_nil environment pattern
            (noFree.1.2 pattern membership)).trans (by simp)

end CostStaticAtomEnvironment

namespace CostStaticRegionNode

/-- A stopped occurrence whose abstract context canonically evaporates is an
exact semantic-atom leaf of the keyed hereditary frame.

The premise is phrased with ordinary canonicalization and the occurrence's
own source name.  Occurrence conservation proves the frame contains no other
free names; the generic filler theorem changes the name to the environment's
atom name; order-agnosticity then transfers the collapse to the keyed
two-depth canonicalizer. -/
theorem stopped_collapse_canonicalFrame
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot)
    (collapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  let declaration :=
    rhoReflectivePresentation.toReflectivePresentationDecl
  have frameFree : contextFrameFreeFvarNames state.skeletonContext = [] :=
    contextFrameFreeFvarNames_eq_nil_of_collapse declaration collapse
  have reifiedContext :
      environment.reifyContext state.skeletonContext = state.skeletonContext :=
    CostStaticAtomEnvironment.reifyContext_eq_self_of_frameFreeFvarNames_eq_nil
      environment
      state.skeletonContext frameFree
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      state.skeletonContext.fill (.fvar (environment.atomName slot)) := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar state.boundaryOccurrence.name)) :=
        congrArg environment.reify state.abstract_eq
      _ = (environment.reifyContext state.skeletonContext).fill
          (environment.reify (.fvar state.boundaryOccurrence.name)) :=
        (environment.reifyContext_fill state.skeletonContext _).symm
      _ = state.skeletonContext.fill
          (.fvar (environment.atomName slot)) := by
        rw [reifiedContext]
        simp only [CostStaticAtomEnvironment.reify]
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have ordinaryCollapse : canonicalize declaration
        (state.skeletonContext.fill (.fvar (environment.atomName slot))) =
      .fvar (environment.atomName slot) := by
    simpa [declaration, canonicalize] using
      canonicalize_fill_eq_of_collapse declaration (by decide) collapse
        (.fvar (environment.atomName slot))
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment, reifiedFrame]
  rw [canonicalizeByDepths_eq_fvar_of_canonicalize_eq _ declaration _ _
    ordinaryCollapse]
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

end CostStaticRegionNode

namespace RhoCollapsingLeafExposure

/-- Close a stopped boundary selected by the intrinsic canonical-collapse
test, without requiring a syntactic shell certificate. -/
noncomputable def stoppedCollapseBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (collapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport : state.certified.typed.boundary.targetSupport.length =
      node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.stopped_collapse_canonicalFrame node environment
      state slot selected collapse
  exact stoppedBoundaryElaborationAlignedSameSupport node children state
    entryEmbedding leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot :=
        Option.some.inj (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment alignedToRight sameSupport

/-- Recursive closure at a stopped occurrence whose surrounding context
canonically evaporates.  The recursive call is made only for the certified
boundary content, which is strictly smaller than the enclosing static root. -/
noncomputable def stoppedCollapseOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
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
    (contextCollapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
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
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
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
  exact stoppedCollapseBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding contextCollapse
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))

/-- Support-independent recursive closure for a collapsing stopped context
whose structural endpoint is a source variable. -/
noncomputable def stoppedCollapseSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (leftView : left.StaticRootView color)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (contextCollapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (.fvar name))
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
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf (Pattern.fvar name) →
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
  have nameLookup : targetFree name = some type := by
    cases rightWellSorted.1.1 with
    | fvar lookup => exact lookup
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType (Pattern.fvar name) := by
    refine ⟨⟨WellSorted.HasType.fvar ?_, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [boundaryType] using nameLookup
    · intro declaration _declarationMembership
      rfl
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content +
          sizeOf (Pattern.fvar name) <
        sizeOf leftPattern + sizeOf (Pattern.fvar name) := by
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
  exact stoppedBoundaryElaborationSourceVariable leftView.node
    leftView.children state entryEmbedding name childPair.leftTree
      childPair.rightTree right
      (fun slot selected =>
        CostStaticRegionNode.stopped_collapse_canonicalFrame leftView.node
          (leftView.node.normalizationEnvironment
            rhoHereditaryStaticNormalizer leftView.children)
          state slot selected contextCollapse)
      childPair.alignment

end RhoCollapsingLeafExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
