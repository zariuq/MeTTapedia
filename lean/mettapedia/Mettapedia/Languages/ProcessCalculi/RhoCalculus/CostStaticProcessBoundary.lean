import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCollapse
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnosticDepths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundVariableExposure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

/-!
# Static process boundaries in the Cost translation of rho

The two static Cost fibres share the rho name sort but have disjoint process
sorts.  This distinction is important below a selected quotation: its payload
has the selected process type, so a collection at that position cannot become
an opposite-colour static boundary.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The process type of one rho static Cost fibre is not decodable in the
opposite fibre.  Unlike the shared name type, it therefore cannot support an
opposite-colour collection plan. -/
theorem rho_decodeCostStaticTypeExpr_flip_process_eq_none
    (color : CostStaticColor) :
    decodeCostStaticTypeExpr rhoCIGSLT color.flip
        (.base
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) = none := by
  have interacting :
      rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := rfl
  cases color with
  | base =>
      have processSort :
          (costStaticReflectivePresentationDecl rhoCIGSLT .base
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort = costBaseSortName "Proc" := by
        simp [costStaticReflectivePresentationDecl_eq_map,
          ReflectionExtension.mapReflectivePresentation,
          rhoReflectivePresentation, CostStaticColor.symbols,
          costBaseStaticSymbols, costBaseLanguageDefSymbolMap]
      rw [processSort]
      rfl
  | wrapped =>
      have processSort :
          (costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort = costWrappedSortName := by
        simp [costStaticReflectivePresentationDecl_eq_map,
          ReflectionExtension.mapReflectivePresentation,
          rhoReflectivePresentation, CostStaticColor.symbols,
          costWrappedStaticSymbols, interacting]
      rw [processSort]
      rfl

/-- No collection typing choice in the opposite static colour can inhabit the
selected rho process fibre. -/
theorem rho_costStaticCollectionTypingChoices_flip_process_eq_nil
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr) (collectionType : CollType)
    (elements : List Pattern) :
    costStaticCollectionTypingChoices rhoCIGSLT color.flip targetFree
        targetBound collectionType elements
        (.base
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) = [] := by
  unfold costStaticCollectionTypingChoices
  rw [rho_decodeCostStaticTypeExpr_flip_process_eq_none]

/-- Source-facing form of
`rho_costStaticCollectionTypingChoices_flip_process_eq_nil`. -/
theorem rho_costStaticCollectionTypingChoices_flip_mappedProcess_eq_nil
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (targetBound : List TypeExpr) (collectionType : CollType)
    (elements : List Pattern) :
    costStaticCollectionTypingChoices rhoCIGSLT color.flip targetFree
        targetBound collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base
            rhoCIGSLT.theory.presentation.interactingSort.1.name)) = [] := by
  have interacting :
      rhoCIGSLT.theory.presentation.interactingSort.1.name = "Proc" := rfl
  convert rho_costStaticCollectionTypingChoices_flip_process_eq_nil color
    targetFree targetBound collectionType elements using 1
  cases color <;>
    simp [costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation,
      rhoReflectivePresentation, CostStaticColor.symbols,
      costBaseStaticSymbols, costBaseLanguageDefSymbolMap,
      costWrappedStaticSymbols, mapTypeExpr, interacting]

/-- A collection that is being planned at the rho process type always has a
current-colour typing choice.  In particular, the planner cannot stop it as an
opposite-colour collection boundary immediately below a selected Quote. -/
theorem CostStaticRegionPlan.exists_currentChoice_of_rhoProcess_collection
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements rest)
      (.base rhoCIGSLT.theory.presentation.interactingSort.1.name)) :
    ∃ choice,
      choice ∈ costStaticCollectionTypingChoices rhoCIGSLT color targetFree
        targetBound collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rhoCIGSLT.theory.presentation.interactingSort.1.name)) := by
  cases plan with
  | collection choice selected children => exact ⟨choice, selected⟩
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      rw [rho_costStaticCollectionTypingChoices_flip_mappedProcess_eq_nil]
        at oppositeSelected
      simp at oppositeSelected

/-- A stopped occurrence whose reified one-hole frame collapses a fresh probe
has the exact keyed canonical-frame equation required by the structural
closure layer.  No syntactic catalogue of Quote/Drop or singleton-parallel
shells is needed. -/
theorem CostStaticRegionNode.stopped_canonicalFrame_of_probeCollapse
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
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
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((environment.reifyContext state.skeletonContext).fill
          (.fvar probe)) = .fvar probe) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      (environment.reifyContext state.skeletonContext).fill
        (.fvar (environment.atomName slot)) := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = (environment.reifyContext state.skeletonContext).fill
          (environment.reify
            (.fvar (costRegionBoundaryVariableName
              state.certified.typed.boundary))) :=
        (environment.reifyContext_fill state.skeletonContext _).symm
      _ = (environment.reifyContext state.skeletonContext).fill
          (.fvar (environment.atomName slot)) := by
        simp only [CostStaticAtomEnvironment.reify]
        change (environment.reifyContext state.skeletonContext).fill
            (.fvar (environment.reifyName state.boundaryOccurrence.name)) = _
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have quoteNeDrop : rhoReflectivePresentation.quoteConstructor ≠
      rhoReflectivePresentation.dropConstructor := by decide
  have ordinaryCollapse : canonicalize rhoReflectivePresentation
      ((environment.reifyContext state.skeletonContext).fill
        (.fvar (environment.atomName slot))) =
      .fvar (environment.atomName slot) := by
    calc
      canonicalize rhoReflectivePresentation
          ((environment.reifyContext state.skeletonContext).fill
            (.fvar (environment.atomName slot))) =
        canonicalize rhoReflectivePresentation
          (.fvar (environment.atomName slot)) :=
        canonicalize_fill_eq_of_collapse rhoReflectivePresentation
          quoteNeDrop collapse (.fvar (environment.atomName slot))
      _ = .fvar (environment.atomName slot) := rfl
  have keyedCollapse := canonicalizeByDepths_eq_fvar_of_canonicalize_eq
    (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
    rhoReflectivePresentation node.targetBound.length 0 ordinaryCollapse
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment, reifiedFrame, keyedCollapse]
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

namespace RhoCollapsingLeafExposure

/-- Close a stopped boundary whenever its fully reified context passes the
single-probe collapse test.  This is the semantic replacement for the former
finite shell catalogue. -/
noncomputable def stoppedProbeCollapseBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        (((node.normalizationEnvironment rhoHereditaryStaticNormalizer
          children).reifyContext state.skeletonContext).fill
            (.fvar probe)) = .fvar probe)
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
  have collapse' : canonicalize rhoReflectivePresentation
      ((environment.reifyContext state.skeletonContext).fill (.fvar probe)) =
      .fvar probe := by
    simpa only [environment] using collapse
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.stopped_canonicalFrame_of_probeCollapse node
      environment state slot selected probe collapse'
  exact stoppedBoundaryElaborationAlignedSameSupport node children state
    entryEmbedding leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot :=
        Option.some.inj (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment alignedToRight sameSupport

/-- Recursive closure for a stopped occurrence satisfying the reified probe
collapse law.  The recursive call is made only for the certified boundary
content, whose size is strictly below the enclosing static root. -/
noncomputable def stoppedProbeCollapseOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
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
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((leftView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer leftView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
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
  exact stoppedProbeCollapseBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding probe collapse
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))

/-- Support-independent closure for a stopped occurrence whose reified frame
passes the probe-collapse test and whose opposite structural endpoint is a
source variable.  Quote-local support may differ; only the selected boundary
type and its recursively normalized value are compared. -/
noncomputable def stoppedProbeCollapseSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
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
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((leftView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer leftView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
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
  let environment := leftView.node.normalizationEnvironment
    rhoHereditaryStaticNormalizer leftView.children
  have collapse' : canonicalize rhoReflectivePresentation
      ((environment.reifyContext state.skeletonContext).fill (.fvar probe)) =
      .fvar probe := by
    simpa only [environment] using collapse
  exact stoppedBoundaryElaborationSourceVariable leftView.node
    leftView.children state entryEmbedding name childPair.leftTree
      childPair.rightTree right
      (fun slot selected =>
        CostStaticRegionNode.stopped_canonicalFrame_of_probeCollapse
          leftView.node environment state slot selected probe collapse')
      childPair.alignment

end RhoCollapsingLeafExposure

namespace RhoCanonicalStaticPairSemanticCut

/-- Left-oriented semantic cut for a stopped occurrence whose reified frame
passes the probe-collapse test. -/
noncomputable def leftStoppedProbeCollapseOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
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
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((leftView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer leftView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
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
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedProbeCollapseOfCloseSmaller left right
      leftView rightWellSorted state entryEmbedding probe collapse
      boundaryCanonical boundarySupport boundaryType closeSmaller)

/-- Right-oriented companion of
`leftStoppedProbeCollapseOfCloseSmaller`. -/
noncomputable def rightStoppedProbeCollapseOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
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
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((rightView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer rightView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
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
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedProbeCollapseOfCloseSmaller right left
      rightView leftWellSorted state entryEmbedding probe collapse
      boundaryCanonical boundarySupport boundaryType
      (fun {childAvailable childOuter leftChild rightChild childType}
        leftChildWellSorted rightChildWellSorted canonical smaller admissible =>
          by
            let paired := Classical.choice
              (closeSmaller (childAvailable := childAvailable)
                (childOuter := childOuter) (leftChild := rightChild)
                (rightChild := leftChild) (childType := childType)
                rightChildWellSorted leftChildWellSorted canonical.symm
                (by simpa [Nat.add_comm] using smaller) admissible)
            exact ⟨paired.symm⟩))

/-- Left-oriented probe-collapse cut with a source-variable endpoint.  This
variant deliberately does not identify the stopped boundary's quote-local
support with the caller availability. -/
noncomputable def leftStoppedProbeCollapseSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((leftView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer leftView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
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
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedProbeCollapseSourceVariableOfCloseSmaller
      left right leftView rightWellSorted state entryEmbedding probe collapse
      boundaryCanonical boundaryType closeSmaller)

/-- Right-oriented source-variable companion of
`leftStoppedProbeCollapseSourceVariableOfCloseSmaller`. -/
noncomputable def rightStoppedProbeCollapseSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {rightPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rightView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] rightView.node.finiteBoundaryTable.entries)
    (probe : String)
    (collapse : canonicalize rhoReflectivePresentation
        ((((rightView.node.normalizationEnvironment
          rhoHereditaryStaticNormalizer rightView.children).reifyContext
            state.skeletonContext).fill (.fvar probe))) = .fvar probe)
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
          sizeOf (Pattern.fvar name) + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedProbeCollapseSourceVariableOfCloseSmaller
      right left rightView leftWellSorted state entryEmbedding probe collapse
      boundaryCanonical boundaryType
      (fun {childAvailable childOuter leftChild rightChild childType}
        rightChildWellSorted leftChildWellSorted canonical smaller admissible =>
          by
            let paired := Classical.choice
              (closeSmaller (childAvailable := childAvailable)
                (childOuter := childOuter) (leftChild := rightChild)
                (rightChild := leftChild) (childType := childType)
                leftChildWellSorted rightChildWellSorted canonical.symm
                (by simpa [Nat.add_comm] using smaller) admissible)
            exact ⟨paired.symm⟩))

/-- Left-oriented semantic cut when ordinary source-frame canonicalization
exposes a rigid bound variable.  Semantic-atom restoration is not involved in
this terminal. -/
noncomputable def leftRigidBVarOfSourceCanonical
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (sourceIndex : Nat)
    (sourceCanonical :
      let values := leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      canonicalize rhoReflectivePresentation
          (leftView.node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment values).1)).1 =
        .bvar sourceIndex)
    (rightNormal :
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      .bvar (leftView.node.thinning.embedIndexAt 0 sourceIndex)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.rigidBVarOfSourceCanonical leftView.node
      leftView.children right sourceIndex sourceCanonical rightNormal)

/-- Right-oriented companion of `leftRigidBVarOfSourceCanonical`. -/
noncomputable def rightRigidBVarOfSourceCanonical
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (sourceIndex : Nat)
    (sourceCanonical :
      let values := rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)
      canonicalize rhoReflectivePresentation
          (rightView.node.reifiedSourceFrame
            (CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment values).1)).1 =
        .bvar sourceIndex)
    (leftNormal :
      (left.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      .bvar (rightView.node.thinning.embedIndexAt 0 sourceIndex)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.rigidBVarOfSourceCanonical rightView.node
      rightView.children left sourceIndex sourceCanonical leftNormal)

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
