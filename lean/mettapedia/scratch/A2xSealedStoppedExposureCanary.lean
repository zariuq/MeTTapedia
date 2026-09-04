import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesAvailableLeaf
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryPlanOccurrenceAvailability

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem stoppedBoundary_targetSupport_eq_nil_of_quoteRootCanary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {payload childAbstract : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (quoteRoot : node.skeleton.1 = .apply "NQuote" [childAbstract]) :
    state.certified.typed.boundary.targetSupport = [] := by
  let rootOccurrence := castCostStaticFVarOccurrenceRoot
    (node.skeleton_pattern.trans
      node.plan.decoration_abstractPattern.symm) state.boundaryOccurrence
  obtain ⟨packed⟩ := CostStaticPlanDecoration.nonempty_abstractOccurrence
    node.plan.decoration rootOccurrence
  rcases packed with ⟨planAvailable, occurrence⟩
  have planFree : WellSorted.ReflectiveSubstitutionBinderFree
      node.plan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      node.plan
      ⟨node.sourceSort.1, rfl⟩
  have availableEqQuote :=
    CostStaticRegionNode.CostStaticRegionPlan.abstractOccurrence_available_eq_quoteLocal
      node.plan planFree occurrence
  have availableEqSupport :=
    CostStaticRegionNode.CostStaticRegionPlan.abstractOccurrence_available_eq_boundarySupport
      node.plan occurrence state.certified.typed.boundary (by
        simp [rootOccurrence])
  have occurrenceSealed :
      CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
          .exposed rootOccurrence.context = .sealed := by
    have filled : state.skeletonContext.fill
          (.fvar state.boundaryOccurrence.name) =
        .apply "NQuote" [childAbstract] := by
      exact state.abstract_eq.symm.trans quoteRoot
    have stateSealed :
        CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
            .exposed state.skeletonContext = .sealed := by
      cases contextEq : state.skeletonContext with
      | hole =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
      | apply constructor before inner after =>
          rw [contextEq, OneHoleContext.fill] at filled
          have constructorEq : constructor = "NQuote" :=
            (Pattern.apply.inj filled).1
          rw [CostStaticAvailabilityRegime.atContext,
            constructorEq, rho_isQuoteConstructor_quote]
          exact CostStaticRegionNode.rhoAvailabilityRegime_atContext_sealed
            inner
      | lambda binder inner =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
      | multiLambda arity binders inner =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
      | substBody inner replacement =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
      | substReplacement body inner =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
      | collection collectionType before inner after rest =>
          rw [contextEq, OneHoleContext.fill] at filled
          cases filled
    dsimp only [rootOccurrence]
    rw [castCostStaticFVarOccurrenceRoot_context]
    change CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
      .exposed state.skeletonContext = .sealed
    exact stateSealed
  have quoteLocalNil :=
    CostStaticRegionNode.rhoCanonicalOccurrenceAvailable_eq_nil_of_atContext_sealed
      node.targetBound rootOccurrence.context occurrenceSealed
  rw [← availableEqSupport, availableEqQuote, quoteLocalNil]

theorem decodeDeclared_foreignQuote_eq_none_canary
    {leftColor rightColor : CostStaticColor}
    (different : leftColor ≠ rightColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT leftColor
        ((rightColor.symbols rhoCIGSLT).constructor "NQuote") = none := by
  cases leftColor <;> cases rightColor <;> simp_all <;> decide

theorem rhoCrossColor_foreignNameRoot_escape_canary
    {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {rightPattern : Pattern} {type : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (rightName : rightView.node.sourceSort.1 = "Name") :
    RhoDescendEscape leftColor
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) := by
  obtain ⟨arguments, _skeletonArguments, patternShape, _skeletonShape⟩ :=
    rhoNameFibre_view_shape rightView rightName
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    leftColor rhoReflectivePresentation.toReflectivePresentationDecl
  let wire := (rightColor.symbols rhoCIGSLT).constructor "NQuote"
  have wireNeQuote : wire ≠ declaration.quoteConstructor := by
    intro equality
    have rightDecoded : decodeCostStaticConstructor rightColor wire =
        some "NQuote" := by
      exact decodeCostStaticConstructor_symbols rhoCIGSLT rightColor "NQuote"
    have leftDecoded : decodeCostStaticConstructor leftColor wire =
        some "NQuote" := by
      rw [equality]
      rw [show declaration.quoteConstructor =
          (leftColor.symbols rhoCIGSLT).constructor "NQuote" by
        exact rhoDecl_quoteConstructor leftColor]
      exact decodeCostStaticConstructor_symbols rhoCIGSLT leftColor "NQuote"
    exact decodeCostStaticConstructor_color_disjoint different leftDecoded
      rightDecoded
  have canonicalShape : canonicalize declaration rightPattern =
      .apply wire (arguments.map (canonicalize declaration)) := by
    rw [patternShape]
    exact canonicalize_apply_of_ne_quote declaration wireNeQuote arguments
  constructor
  · intro collectionType elements rest equality
    rw [canonicalShape] at equality
    cases equality
  · exact ⟨wire, arguments.map (canonicalize declaration), canonicalShape,
      decodeDeclared_foreignQuote_eq_none_canary different⟩

structure RhoCrossColorSealedDescentCanary
    {declarationColor leftColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    (leftView : left.StaticRootView leftColor) where
  payload : Pattern
  state : CostStaticPlanStopped rhoCIGSLT leftColor targetFree payload
    leftView.node.skeleton.1
  contextCollapse : canonicalize
      rhoReflectivePresentation.toReflectivePresentationDecl
      (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
    .fvar state.boundaryOccurrence.name
  entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT leftColor targetFree
    [state.certified.typed] leftView.node.finiteBoundaryTable.entries
  boundaryCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      state.certified.typed.boundary.content =
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern
  boundarySupport : state.certified.typed.boundary.targetSupport = []

theorem rhoCrossColor_leftCollapsing_sealedDescent_canary
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (sourceSortEq : leftView.node.sourceSort.1 =
      rightView.node.sourceSort.1)
    (notInteracting : leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    Nonempty (RhoCrossColorSealedDescentCanary
      (declarationColor := declarationColor) (rightPattern := rightPattern)
      leftView) := by
  have leftName : leftView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting notInteracting
  have rightName : rightView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting (sourceSortEq ▸ notInteracting)
  obtain ⟨_argument, declarationEq, _patternShape, _argumentCanonical⟩ :=
    CostHereditaryCrossColorLeafHinge.rhoCrossColor_orientedPack_left
      leftView rightView different sourceSortEq notInteracting collapsing
        canonical
  have targetEscape : RhoDescendEscape leftColor
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :=
    rhoCrossColor_foreignNameRoot_escape_canary rightView different rightName
  have planCanonical : canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftView.node.term.1 =
    canonicalize
      (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern := by
    rw [leftView.patternEq]
    simpa only [declarationEq] using canonical
  obtain ⟨payload, ⟨descent⟩⟩ := rhoDescend
    (sizeOf leftView.node.term.1) leftView.node.plan 0
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
      (Nat.le_refl _) (by simpa only [iterDrop] using planCanonical)
      targetEscape
  let state : CostStaticPlanStopped rhoCIGSLT leftColor targetFree payload
      leftView.node.skeleton.1 :=
    { descent.1 with
      abstract_eq := leftView.node.skeleton_pattern.trans
        descent.1.abstract_eq }
  have contextCollapse : canonicalize
      rhoReflectivePresentation.toReflectivePresentationDecl
      (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name := by
    simpa only [state, iterDrop,
      CostStaticPlanStopped.boundaryOccurrence_name] using descent.2.1
  have entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT leftColor
      targetFree [state.certified.typed]
      leftView.node.finiteBoundaryTable.entries := by
    change CostStaticPlanEntryEmbedding rhoCIGSLT leftColor targetFree
      [descent.1.certified.typed] leftView.node.plan.boundaryTable.entries
    exact descent.2.2.1.some
  obtain ⟨_skeletonArgument, childAbstract, _rootPattern, skeletonShape⟩ :=
    CostHereditaryCrossColorLeafHinge.rhoCrossColor_rootSkeleton_singleton
      leftView leftName
  have boundarySupport : state.certified.typed.boundary.targetSupport = [] :=
    stoppedBoundary_targetSupport_eq_nil_of_quoteRootCanary leftView.node state
      skeletonShape
  exact ⟨
    { payload := payload
      state := state
      contextCollapse := contextCollapse
      entryEmbedding := entryEmbedding
      boundaryCanonical := by
        simpa only [state, declarationEq] using descent.2.2.2
      boundarySupport := boundarySupport }⟩

/-- A stopped boundary under a source-rho `Name` skeleton remains in the
same exact generated `Name` fibre.  The proof deliberately uses the typed
authored skeleton and rho's source canonicalizer, not the false mixed-colour
Cost canonicalizer fibre-stability statement. -/
theorem stoppedBoundary_targetType_eq_of_nameRootCanary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (nameRoot : node.sourceSort.1 = "Name")
    (contextCollapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill
          (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name) :
    state.certified.typed.boundary.targetType =
      mapTypeExpr (color.symbols rhoCIGSLT) (.base "Name") := by
  have boundaryMember : state.certified.typed ∈
      node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have filledEq :
      state.skeletonContext.fill (.fvar state.boundaryOccurrence.name) =
        node.skeleton.1 := by
    simpa only [state.boundaryOccurrence_name] using state.abstract_eq.symm
  have filledTyped : HasType rhoCalc node.boundaryTable.sourceFreeContext
      node.sourceBound
      (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name))
      (.base "Name") := by
    have rootTyped := node.skeleton.toCore.2.1
    change HasType rhoCalc node.boundaryTable.sourceFreeContext
      node.sourceBound node.skeleton.1 (.base node.sourceSort.1) at rootTyped
    rw [filledEq]
    simpa only [nameRoot] using rootTyped
  have filledObject : WellSorted.isObjectPattern
      (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      true := by
    have rootObject := node.skeleton.toCore.2.2.2.1
    rw [filledEq]
    exact rootObject
  have pureCanonicalTyped : HasType rhoCalc
      node.boundaryTable.sourceFreeContext node.sourceBound
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)))
      (.base "Name") :=
    LanguageDefCanonicalSection.canonicalize_name_hasSort filledTyped
      filledObject
  have derivedCanonicalTyped : HasType rhoCalc
      node.boundaryTable.sourceFreeContext node.sourceBound
      (canonicalize rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)))
      (.base "Name") := by
    rw [CanonicalMatch.derivedCanonicalize_eq]
    exact pureCanonicalTyped
  rw [contextCollapse] at derivedCanonicalTyped
  have sourceLookup := node.boundaryTable.sourceFreeContext_boundaryVariable
    state.certified.typed boundaryMember
  have sourceTypeEq : state.certified.typed.boundary.type = .base "Name" := by
    cases derivedCanonicalTyped with
    | fvar canonicalLookup =>
        exact Option.some.inj (sourceLookup.symm.trans canonicalLookup)
  have typeMap := node.plan.boundaryTable_fiberCoherent.typeMap
    state.certified.typed boundaryMember
  exact typeMap.symm.trans (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
    sourceTypeEq)

noncomputable def sealedStoppedCollapseOfCloseSmallerCanary
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
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
      state.certified.typed.boundary.targetSupport = [])
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
  have boundaryWellSortedAtRoot : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type state.certified.typed.boundary.content := by
    have atNil : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree [] type state.certified.typed.boundary.content := by
      simpa only [boundarySupport, boundaryType] using boundaryWellSorted
    simpa using atNil.extendOuter available
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
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSortedAtRoot rightWellSorted
      boundaryCanonical boundarySmaller admissible)
  let environment := leftView.node.normalizationEnvironment
    rhoHereditaryStaticNormalizer leftView.children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have staticFrame :
      leftView.node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.stopped_collapse_canonicalFrame leftView.node
      environment state slot selected contextCollapse
  let selectedTree := state.selectedTreeFromForest entryEmbedding
    leftView.children
  have selectedToPair :
      (selectedTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (childPair.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    apply CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
      (smallAvailable := state.certified.typed.boundary.targetSupport)
      (largeAvailable := available) (ambient := available)
        (small := selectedTree) (large := childPair.leftTree)
    · simp [boundarySupport]
    · rfl
    · exact boundaryType
    · exact state.certified.typed.contentObjectPattern
  have pairNormal :
      (childPair.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simpa only [rhoHereditaryNormalizationKernel] using
      childPair.alignment.normalize_pattern_eq
  let ambientRight := childPair.rightTree.extendOuter outer
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    (childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightWellSorted.1.2.2.1
  have selectedNormal :
      (selectedTree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact selectedToPair.trans
      (pairNormal.trans (childToAmbient.trans ambientToRight))
  have atomEq := state.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition entryEmbedding
      leftView.children environment slot selected
  have atomToSelected : (environment.atomValue slot).key.normal =
      (selectedTree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 := by
    have normalEq := congrArg (fun atom => atom.key.normal) atomEq
    simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
  have environmentSealed :
      (environment.atomValue slot).key.targetSupport = [] := by
    have supportEq := congrArg (fun atom => atom.key.targetSupport) atomEq
    simpa only [TypedCostStaticAtom.ofBoundaryValue, boundarySupport] using
      supportEq
  have normalScoped :
      (environment.atomValue slot).key.normal.isWellScopedAt 0 = true :=
    RhoMatchedStaticFramesApex.atomNormalScopedAtZero_of_targetSupport_nil
      environment slot environmentSealed
  exact RhoCollapsingLeafExposure.atomOfNormal leftView.node
    leftView.children right slot staticFrame
      (atomToSelected.trans selectedNormal) normalScoped

theorem rhoCrossColor_leftCollapsing_leafExposure_canary
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (sourceSortEq : leftView.node.sourceSort.1 =
      rightView.node.sourceSort.1)
    (notInteracting : leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (_leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    Nonempty (RhoCollapsingLeafExposure leftView.node leftView.children
      right) := by
  obtain ⟨descent⟩ := rhoCrossColor_leftCollapsing_sealedDescent_canary
    leftView rightView different sourceSortEq notInteracting collapsing
      canonical
  have leftName : leftView.node.sourceSort.1 = "Name" :=
    rho_sourceSort_eq_name_of_ne_interacting notInteracting
  have boundaryName := stoppedBoundary_targetType_eq_of_nameRootCanary
    leftView.node descent.state descent.entryEmbedding leftName
      descent.contextCollapse
  have mappedName : mapTypeExpr (leftColor.symbols rhoCIGSLT)
      (.base "Name") =
      .base (leftColor.mapLangSort rhoCIGSLT leftView.node.sourceSort).1 := by
    change TypeExpr.base ((leftColor.symbols rhoCIGSLT).sort "Name") =
      TypeExpr.base
        ((leftColor.symbols rhoCIGSLT).sort leftView.node.sourceSort.1)
    rw [leftName]
  have boundaryType : descent.state.certified.typed.boundary.targetType =
      type := boundaryName.trans (mappedName.trans leftView.typeEq)
  exact ⟨sealedStoppedCollapseOfCloseSmallerCanary left right leftView
    admissible rightWellSorted descent.state descent.entryEmbedding
      descent.contextCollapse descent.boundaryCanonical descent.boundarySupport
      boundaryType closeSmaller⟩

theorem rhoCrossColor_rightCollapsing_leafExposure_canary
    {declarationColor leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    (sourceSortEq : leftView.node.sourceSort.1 =
      rightView.node.sourceSort.1)
    (notInteracting : leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (_rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    Nonempty (RhoCollapsingLeafExposure rightView.node rightView.children
      left) := by
  have rightNotInteracting : rightView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name :=
    sourceSortEq ▸ notInteracting
  have closeSwapped : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf rightPattern + sizeOf leftPattern) := by
    rw [Nat.add_comm]
    exact closeSmaller
  exact rhoCrossColor_leftCollapsing_leafExposure_canary
    rightView leftView different.symm sourceSortEq.symm rightNotInteracting
      admissible _rightWellSorted leftWellSorted closeSwapped collapsing
      canonical.symm

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
