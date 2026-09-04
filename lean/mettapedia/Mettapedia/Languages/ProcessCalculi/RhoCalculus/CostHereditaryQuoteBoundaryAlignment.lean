import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAvailabilityTransposition
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

mutual
  /-- Reverse a stopped canonical alignment while weakening its delegated
  leaf relation. -/
  theorem CanonicalStopAligned.flip_mono
      {declaration : ReflectivePresentationDecl}
      {relation transposed : Pattern → Pattern → Prop}
      (weaken : ∀ {left right}, relation left right →
        transposed right left) :
      ∀ {left right}, CanonicalStopAligned declaration relation left right →
        CanonicalStopAligned declaration transposed right left
    | _, _, .leaf related => .leaf (weaken related)
    | _, _, .bvar index => .bvar index
    | _, _, .fvar name => .fvar name
    | _, _, .apply different arguments =>
        .apply different (CanonicalStopAlignedList.flip_mono weaken arguments)
    | _, _, .lambda binder body =>
        .lambda binder (CanonicalStopAligned.flip_mono weaken body)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders
          (CanonicalStopAligned.flip_mono weaken body)
    | _, _, .subst body replacement =>
        .subst (CanonicalStopAligned.flip_mono weaken body)
          (CanonicalStopAligned.flip_mono weaken replacement)
    | _, _, .collection different elements =>
        .collection different
          (CanonicalStopAlignedList.flip_mono weaken elements)
    | _, _, .collectionRest collectionType rest elements =>
        .collectionRest collectionType rest
          (CanonicalStopAlignedList.flip_mono weaken elements)

  /-- Listwise companion of `CanonicalStopAligned.flip_mono`. -/
  theorem CanonicalStopAlignedList.flip_mono
      {declaration : ReflectivePresentationDecl}
      {relation transposed : Pattern → Pattern → Prop}
      (weaken : ∀ {left right}, relation left right →
        transposed right left) :
      ∀ {left right},
        CanonicalStopAlignedList declaration relation left right →
          CanonicalStopAlignedList declaration transposed right left
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (CanonicalStopAligned.flip_mono weaken head)
          (CanonicalStopAlignedList.flip_mono weaken tail)
end

/-- Availability transposition out of an authored Quote needs no recursive
boundary-reexposure callback.  Every boundary in the Quote-root plan is
sealed at empty target support, contradicting the callback's nonempty-support
guard. -/
theorem CostStaticRegionNode.normalizeHereditary_availabilityTransposed_eq_of_forests_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallNode.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largeNode.boundaryTable)
    {ambient : List TypeExpr}
    (targetBoundEq : largeNode.targetBound = smallNode.targetBound ++ ambient)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallNode.boundaryTable
        largeNode.boundaryTable smallTrees largeTrees)
    (sourcePlanAligned : CostStaticAbstractPatternAlignment
      smallNode.boundaryTable.entries largeNode.boundaryTable.entries
      ambient .exposed smallNode.skeleton.1 largeNode.skeleton.1)
    (quoteRoot : smallNode.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    (normalizeHereditary smallNode
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 =
    (normalizeHereditary largeNode
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  have frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      smallNode.plan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      smallNode.plan ⟨smallNode.sourceSort.1, rfl⟩
  apply CostStaticRegionNode.normalizeHereditary_availabilityTransposed_eq_of_forests
    smallNode largeNode smallTrees largeTrees targetBoundEq forests
      sourcePlanAligned
  dsimp only
  intro _current smallPosition _largePosition _positionEq _sealed
    nonemptySupport
  exact (nonemptySupport
    (CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
      smallNode.plan frameFree _ (List.get_mem _ _) quoteRoot)).elim

noncomputable def CostRegionBoundaryTrees.ofTypedTable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences) :
    CostRegionBoundaryTrees source targetFree color table :=
  CostRegionBoundaryTrees.ofTable table (fun boundary _membership =>
    (CostRegionTree.build? (source := source) (targetFree := targetFree)
      boundary.boundary.targetSupport [] boundary.boundary.content
        boundary.boundary.targetType).get
      (CostRegionTree.build?_isSome_of_wellSorted
        ⟨⟨boundary.contentTyped,
            boundary.contentCanonicalBinderMetadata,
            boundary.contentObjectPattern,
            boundary.contentTyped.isWellScopedAt⟩,
          boundary.contentReflectiveScopeSafe⟩))

def CostRegionTree.reindexFiber
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {firstAvailable secondAvailable outer : List TypeExpr}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (availableEq : firstAvailable = secondAvailable)
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (tree : CostRegionTree source targetFree firstAvailable outer firstPattern
      firstType) :
    CostRegionTree source targetFree secondAvailable outer secondPattern
      secondType := by
  cases availableEq
  cases patternEq
  cases typeEq
  exact tree

@[simp]
theorem CostRegionTree.reindexFiber_normalize_pattern
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {firstAvailable secondAvailable outer : List TypeExpr}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (availableEq : firstAvailable = secondAvailable)
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (tree : CostRegionTree source targetFree firstAvailable outer firstPattern
      firstType) (normalizeStatic : CostStaticRegionNormalizer source) :
    ((CostRegionTree.reindexFiber availableEq patternEq typeEq tree).normalize
      (normalizeStatic := normalizeStatic)).pattern =
        (tree.normalize (normalizeStatic := normalizeStatic)).pattern := by
  cases availableEq
  cases patternEq
  cases typeEq
  rfl

theorem CostRegionBoundaryTrees.getEntry_normal_eq_of_availabilitySuffix
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {ambient : List TypeExpr} {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    (tables : TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
      smallTable largeTable)
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable)
    (smallPosition : Fin smallTable.entries.length)
    (largePosition : Fin largeTable.entries.length)
    (positionEq : smallPosition.1 = largePosition.1)
    (supportEq :
      (smallTable.entries.get smallPosition).boundary.targetSupport =
        (largeTable.entries.get largePosition).boundary.targetSupport) :
    ((smallTrees.getEntry smallPosition).tree.normalize
        (normalizeStatic := kernel.normalize)).pattern =
      ((largeTrees.getEntry largePosition).tree.normalize
        (normalizeStatic := kernel.normalize)).pattern := by
  let canonicalLargePosition : Fin largeTable.entries.length :=
    Fin.cast (TypedCostRegionBoundaryTable.AvailabilitySuffix.entries_length_eq
      tables) smallPosition
  have largePositionEq : canonicalLargePosition = largePosition := by
    apply Fin.ext
    exact positionEq
  subst largePosition
  have boundarySuffix := tables.getEntry smallPosition
  let smallBoundary := smallTrees.getEntry smallPosition
  let largeBoundary := largeTrees.getEntry canonicalLargePosition
  have smallBoundaryEq : smallBoundary.boundary =
      smallTable.entries.get smallPosition :=
    smallTrees.getEntry_boundary smallPosition
  have largeBoundaryEq : largeBoundary.boundary =
      largeTable.entries.get canonicalLargePosition :=
    largeTrees.getEntry_boundary canonicalLargePosition
  have targetSupportEq : smallBoundary.boundary.boundary.targetSupport =
      largeBoundary.boundary.boundary.targetSupport := by
    simpa only [smallBoundaryEq, largeBoundaryEq] using supportEq
  have targetTypeEq : smallBoundary.boundary.boundary.targetType =
      largeBoundary.boundary.boundary.targetType := by
    simpa only [smallBoundaryEq, largeBoundaryEq] using
      boundarySuffix.targetType_eq
  have contentEq : smallBoundary.boundary.boundary.content =
      largeBoundary.boundary.boundary.content := by
    simpa only [smallBoundaryEq, largeBoundaryEq] using
      boundarySuffix.content_eq
  let largeTree : CostRegionTree source targetFree
      smallBoundary.boundary.boundary.targetSupport []
      smallBoundary.boundary.boundary.content
      smallBoundary.boundary.boundary.targetType :=
    CostRegionTree.reindexFiber targetSupportEq.symm contentEq.symm
      targetTypeEq.symm largeBoundary.tree
  have normalized := CostRegionTree.normalize_pattern_eq_of_unambiguous
    unambiguous kernel smallBoundary.tree largeTree
      smallBoundary.boundary.contentObjectPattern
  exact normalized.trans (by
    simp [smallBoundary, largeBoundary, largeTree])

theorem CostStaticPlanReached.exists_visibleQuoteRootTree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ (sealed : List TypeExpr)
        (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
          (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable .hole payload reached.sourceType)
        (_rootStatic : rootPlan.isStaticRoot = true)
        (node : CostStaticRegionNode rhoCIGSLT color targetFree)
        (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
          node.finiteBoundaryTable),
      reached.targetBound = reached.sourceAvailable ++ sealed ∧
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
        rootPlan (reached.plan.recontextualize .hole) ∧
      node.targetBound = reached.sourceAvailable ∧
      node.term.1 = payload ∧
      node.plan.boundaryTable.entries = rootPlan.boundaryTable.entries ∧
      node.plan.abstractPattern = rootPlan.abstractPattern ∧
      ((CostRegionTree.static (outer := []) node children).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        ((reached.payloadTreeOfWellSorted admission.wellSorted).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  rcases reached with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  let state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract :=
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  change state.plan.RawAdmission at admission
  change state.plan.rootClass = .application
    rhoReflectivePresentation.quoteConstructor at quoteRoot
  change ∃ (sealed : List TypeExpr)
      (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
        (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
          state.sourceAvailable)
        state.sourceAvailable
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
          state.sourceAvailable)
        state.sourceAvailable .hole payload state.sourceType)
      (_rootStatic : rootPlan.isStaticRoot = true)
      (node : CostStaticRegionNode rhoCIGSLT color targetFree)
      (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
        node.finiteBoundaryTable),
    state.targetBound = state.sourceAvailable ++ sealed ∧
    CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
      rootPlan (state.plan.recontextualize .hole) ∧
    node.targetBound = state.sourceAvailable ∧
    node.term.1 = payload ∧
    node.plan.boundaryTable.entries = rootPlan.boundaryTable.entries ∧
    node.plan.abstractPattern = rootPlan.abstractPattern ∧
    ((CostRegionTree.static (outer := []) node children).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((state.payloadTreeOfWellSorted admission.wellSorted).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern
  obtain ⟨sealed, rootPlan, split, rootBuilt, rootStatic, aligned⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_staticRootPlanSealedAlignment_of_quoteRoot
      state admission quoteRoot
  have sourceTypeName :=
    rho_applicationPlan_sourceType_eq_name_of_quoteRoot state.plan quoteRoot
  change sourceType = .base "Name" at sourceTypeName
  subst sourceType
  let rootTerm : WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage targetFree
      state.sourceAvailable (color.mapLangSort rhoCIGSLT rhoName) := by
    refine ⟨payload, ?_⟩
    change WellSorted.OpenPatternWellSorted rhoCIGSLT.costWholeLanguage
      targetFree state.sourceAvailable
        (.base (color.mapLangSort rhoCIGSLT rhoName).1) payload
    simpa [state, rhoName, mapTypeExpr,
      CostStaticColor.mapLangSort_name] using admission.wellSorted.1
  let rootNamePlan := rootPlan
  have rootNameStatic : rootNamePlan.isStaticRoot = true := rootStatic
  let node : CostStaticRegionNode rhoCIGSLT color targetFree :=
    CostStaticRegionNode.ofPlan (sourceSort := rhoName) rootTerm rootNamePlan
      rootNameStatic
  let children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable := CostRegionBoundaryTrees.ofTypedTable _
  refine ⟨sealed, rootPlan, rootStatic, node, children, split, aligned, rfl,
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel
    (CostRegionTree.static (outer := []) node children)
    (state.payloadTreeOfWellSorted admission.wellSorted)
    admission.object

/-- Rebuild an admitted reached bare parallel at its visible `Proc` root.

The reached plan may sit below a contextual binder suffix, but recompiling the
same payload at its own active availability produces a static collection node.
The hereditary normal of that node is independent of the proof-relevant tree
chosen for the admitted payload. -/
theorem CostStaticPlanReached.exists_visibleParallelRootTree
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (parallelRoot : reached.plan.rootClass = .collection
      rhoReflectivePresentation.parallelCollection)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType)) :
    ∃ (sealed : List TypeExpr)
        (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
          (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable .hole payload reached.sourceType)
        (_rootStatic : rootPlan.isStaticRoot = true)
        (node : CostStaticRegionNode rhoCIGSLT color targetFree)
        (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
          node.finiteBoundaryTable),
      reached.targetBound = reached.sourceAvailable ++ sealed ∧
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
        rootPlan (reached.plan.recontextualize .hole) ∧
      node.targetBound = reached.sourceAvailable ∧
      node.term.1 = payload ∧
      node.plan.boundaryTable.entries = rootPlan.boundaryTable.entries ∧
      node.plan.abstractPattern = rootPlan.abstractPattern ∧
      ((CostRegionTree.static (outer := []) node children).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        ((reached.payloadTreeOfWellSorted admission.wellSorted).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  rcases reached with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  let state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract :=
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  change state.plan.RawAdmission at admission
  change state.plan.rootClass = .collection
    rhoReflectivePresentation.parallelCollection at parallelRoot
  change rhoCanonicalRecursiveTypeDomain.Admissible
    (mapTypeExpr (color.symbols rhoCIGSLT) state.sourceType) at admissible
  change ∃ (sealed : List TypeExpr)
      (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
        (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
          state.sourceAvailable)
        state.sourceAvailable
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
          state.sourceAvailable)
        state.sourceAvailable .hole payload state.sourceType)
      (_rootStatic : rootPlan.isStaticRoot = true)
      (node : CostStaticRegionNode rhoCIGSLT color targetFree)
      (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
        node.finiteBoundaryTable),
    state.targetBound = state.sourceAvailable ++ sealed ∧
    CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
      rootPlan (state.plan.recontextualize .hole) ∧
    node.targetBound = state.sourceAvailable ∧
    node.term.1 = payload ∧
    node.plan.boundaryTable.entries = rootPlan.boundaryTable.entries ∧
    node.plan.abstractPattern = rootPlan.abstractPattern ∧
    ((CostRegionTree.static (outer := []) node children).normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      ((state.payloadTreeOfWellSorted admission.wellSorted).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern
  obtain ⟨elements, rest, payloadEq⟩ :=
    CostStaticRegionPlan.collectionRoot_of_rootClass state.plan parallelRoot
  subst payload
  obtain ⟨sealed, rootPlan, split, _rootBuilt, aligned⟩ :=
    state.exists_rootPlanSealedAlignment
      CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
      admission
  have sourceTypeProc := rho_collectionPlan_sourceType_eq_proc state.plan
    ⟨rhoReflectivePresentation.parallelCollection, parallelRoot⟩ admissible
  change sourceType = .base "Proc" at sourceTypeProc
  subst sourceType
  have rootStatic : rootPlan.isStaticRoot = true :=
    rho_collectionPlan_isStaticRoot rootPlan
  let rootTerm : WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage targetFree
      state.sourceAvailable (color.mapLangSort rhoCIGSLT rhoProc) := by
    refine ⟨.collection rhoReflectivePresentation.parallelCollection elements
      rest, ?_⟩
    change WellSorted.OpenPatternWellSorted rhoCIGSLT.costWholeLanguage
      targetFree state.sourceAvailable
        (.base (color.mapLangSort rhoCIGSLT rhoProc).1)
        (.collection rhoReflectivePresentation.parallelCollection elements
          rest)
    simpa [state, rhoProc, mapTypeExpr] using admission.wellSorted.1
  let node : CostStaticRegionNode rhoCIGSLT color targetFree :=
    CostStaticRegionNode.ofPlan (sourceSort := rhoProc) rootTerm rootPlan
      rootStatic
  let children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable := CostRegionBoundaryTrees.ofTypedTable _
  refine ⟨sealed, rootPlan, rootStatic, node, children, split, aligned, rfl,
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel
    (CostRegionTree.static (outer := []) node children)
    (state.payloadTreeOfWellSorted admission.wellSorted)
    admission.object

/-- A recursively flattened parallel leaf retains the exact reached-or-stopped
plan view at its source occurrence, together with the proof-relevant embedding
of every retained boundary entry into the enclosing plan table. -/
theorem CostStaticRegionPlan.nonempty_shapedContextInventoryView_of_parallelLeaf
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern leaf : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (declaration : ReflectivePresentationDecl)
    (membership : leaf ∈
      RhoCommonRestorationApex.parallelLeaves declaration pattern) :
    Nonempty (CostStaticPlanShapedContextInventoryView rhoCIGSLT color
      targetFree leaf plan.abstractPattern plan.boundaryTable.entries) := by
  obtain ⟨context, shape⟩ :=
    RhoCommonRestorationApex.parallelLeaves_context declaration pattern leaf
      membership
  exact plan.nonempty_shapedContextInventoryView context shape

/-- Traversing a rho static plan through a context made only of bare-parallel
frames always reaches the selected payload.  It cannot stop at an application
boundary because the context has no application frame, and rho admits no
foreign boundary-collection plan.  The returned embedding retains the exact
finite boundary positions of the reached subplan in the enclosing plan. -/
theorem CostStaticRegionPlan.exists_reached_of_parallelLeafContext
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (declaration : ReflectivePresentationDecl) :
    ∀ {context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext},
      RhoCommonRestorationApex.ParallelLeafContext declaration context →
      ∀ {sourceBound targetBound : List TypeExpr}
        {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
          targetBound}
        {sourceAvailable : List TypeExpr}
        {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
        {pattern payload : Pattern} {sourceType : TypeExpr}
        (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
          targetBound thinning sourceAvailable outer pattern sourceType),
        pattern = context.fill payload →
        ∃ reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
            plan.abstractPattern,
          Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
            reached.plan.boundaryTable.entries plan.boundaryTable.entries)
  | _, .hole, _, _, _, _, _, pattern, payload, _, plan, fillEq => by
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
        at fillEq
      subst pattern
      exact ⟨
        { sourceBound := _, targetBound := _, thinning := _
          sourceAvailable := _, outer := _, sourceType := _
          plan := plan, skeletonContext := .hole, abstract_eq := rfl },
        ⟨CostStaticPlanEntryEmbedding.refl _⟩⟩
  | _, .collection before after innerShape, _, _, _, _, _, pattern, payload,
      _, plan, fillEq => by
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill]
        at fillEq
      cases plan with
      | bvar sourceIndex lookup correspondence availableScope =>
          simp at fillEq
      | fvar lookup => simp at fillEq
      | boundaryApplication constructor rendered outsideCurrent certified
          certifies => simp at fillEq
      | application constructor rendered current preimage notBare children =>
          simp at fillEq
      | lambda bodyPlan => simp at fillEq
      | multiLambda bodyPlan => simp at fillEq
      | boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies =>
          exact (rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
            oppositeSelected currentRejected).elim
      | @collection _ _ _ _ _ planCollection _ planRest _ choice selected
          children =>
          obtain ⟨-, elementsEq, -⟩ := Pattern.collection.inj fillEq
          obtain ⟨active⟩ :=
            CostStaticElementPlan.nonempty_activeAt children elementsEq
          obtain ⟨reached, ⟨embedding⟩⟩ :=
            CostStaticRegionPlan.exists_reached_of_parallelLeafContext
              declaration innerShape active.head rfl
          let frame :
              Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext :=
            .collection planCollection active.beforeAbstracts .hole
              active.afterAbstracts
              (planRest.map costRegionSourceVariableName)
          refine ⟨reached.rebaseAbstractRoot frame ?_,
            ⟨embedding.comp active.entryEmbedding⟩⟩
          simp [CostStaticRegionPlan.abstractPattern, frame,
            Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
            active.abstracts_eq]

/-- Every recursively flattened parallel leaf of a rho plan has an exact
reached subplan and a proof-relevant entry embedding into the root plan. -/
theorem CostStaticRegionPlan.exists_reached_of_parallelLeaf
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern leaf : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (declaration : ReflectivePresentationDecl)
    (membership : leaf ∈
      RhoCommonRestorationApex.parallelLeaves declaration pattern) :
    ∃ reached : CostStaticPlanReached rhoCIGSLT color targetFree leaf
        plan.abstractPattern,
      Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
        reached.plan.boundaryTable.entries plan.boundaryTable.entries) := by
  obtain ⟨context, contextShape, fillEq⟩ :=
    RhoCommonRestorationApex.parallelLeaves_parallelContext declaration pattern
      leaf membership
  exact CostStaticRegionPlan.exists_reached_of_parallelLeafContext declaration
    contextShape plan fillEq

/-- A proof-relevant tree for the payload of an admitted reached Quote has a
static root at the Quote plan's selected colour. -/
theorem CostStaticPlanReached.nonempty_staticRootView_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType)) :
    Nonempty (tree.StaticRootView color) := by
  obtain ⟨wireName, arguments, constructor, payloadEq, decoded, role⟩ :=
    CostStaticRegionPlan.staticApplicationData_of_quoteRoot reached.plan
      quoteRoot
  have sourceTypeName :=
    rho_applicationPlan_sourceType_eq_name_of_quoteRoot reached.plan quoteRoot
  obtain ⟨root⟩ :=
    tree.nonempty_staticRootColor_of_static_application_of_eq
      (category := (color.symbols rhoCIGSLT).sort "Name") payloadEq
      (by simp [sourceTypeName, mapTypeExpr]) color constructor decoded role
  exact ⟨root.toView⟩

/-- Reindex only the raw-pattern and authored-source-type fibres of a static
region plan. -/
def CostStaticRegionPlan.reindexPatternSourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer firstPattern firstType) :
    CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer secondPattern secondType := by
  cases patternEq
  cases typeEq
  exact plan

@[simp]
theorem CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer firstPattern firstType) :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      patternEq typeEq plan).boundaryTable.entries =
      plan.boundaryTable.entries := by
  cases patternEq
  cases typeEq
  rfl

@[simp]
theorem CostStaticRegionPlan.reindexPatternSourceType_abstractPattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer firstPattern firstType) :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      patternEq typeEq plan).abstractPattern =
      plan.abstractPattern := by
  cases patternEq
  cases typeEq
  rfl

@[simp]
theorem CostStaticRegionPlan.reindexPatternSourceType_rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer firstPattern firstType) :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      patternEq typeEq plan).rootClass = plan.rootClass := by
  cases patternEq
  cases typeEq
  rfl

@[simp]
theorem CostStaticRegionPlan.recontextualize_rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer newOuter : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType) :
    (plan.recontextualize newOuter).rootClass = plan.rootClass := by
  cases plan <;> rfl

/-- A plan classified at the authored Quote constructor has that constructor
at the root of its abstract source pattern. -/
theorem CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ arguments, plan.abstractPattern = .apply
      rhoReflectivePresentation.quoteConstructor arguments := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have constructorEq : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using
          CostStaticPlanRootClass.application.inj quoteRoot
      exact ⟨children.abstractPatterns, by
        simp [CostStaticRegionPlan.abstractPattern, constructorEq]⟩
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- Transport the source list index of a replayable entry embedding. -/
def CostStaticPlanEntryEmbedding.castSource
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {first second large :
      List (TypedCostRegionBoundary source color targetFree)}
    (sourceEq : first = second)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree first
      large) :
    CostStaticPlanEntryEmbedding source color targetFree second large := by
  cases sourceEq
  exact embedding

/-- A static view over a tree whose target type is a mapped authored type
recovers that authored source type exactly. -/
theorem CostRegionTree.StaticRootView.sourceType_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern}
    {sourceType : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern
      (mapTypeExpr (color.symbols source) sourceType)}
    (view : tree.StaticRootView color) :
    (.base view.node.sourceSort.1 : TypeExpr) = sourceType := by
  apply mapTypeExpr_costStatic_injective source color
  simpa only [mapTypeExpr, CostStaticColor.mapLangSort_name] using view.typeEq

/-- A static root view of the visible Quote payload carries the exact sealed
planner relation to the contextual reached plan. -/
theorem CostStaticPlanReached.staticRootView_boundaryFibersAvailabilitySuffix
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType))
    (view : tree.StaticRootView color) :
    let largePlan :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
        view.patternEq.symm
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostRegionTree.StaticRootView.sourceType_eq
            view).symm
          (reached.plan.recontextualize .hole)
    ∃ sealed,
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
        view.node.plan largePlan ∧
      largePlan.boundaryTable.entries = reached.plan.boundaryTable.entries ∧
      largePlan.abstractPattern = reached.plan.abstractPattern := by
  dsimp only
  obtain ⟨sealed, split⟩ := admission.targetBound_split
  refine ⟨sealed, ?_, ?_, ?_⟩
  apply CostStaticRegionPlan.boundaryFibersAvailabilitySuffix_of_scoped
    CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
      (regime := .sealed)
  · exact view.availableEq.symm
  · simpa only [view.availableEq] using split
  · rfl
  · simpa only [view.patternEq] using admission.object
  · simpa only [view.patternEq, view.availableEq] using
      admission.wellSorted.1.1.isWellScopedAt
  · simp only [CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries,
      CostStaticRegionPlan.recontextualizeEntriesEq]
  · simp only [CostStaticRegionPlan.reindexPatternSourceType_abstractPattern,
      CostStaticRegionPlan.recontextualizeAbstractEq]

/-- A static rho plan at the generated Quote constructor has the authored
Quote root class. -/
theorem CostStaticRegionPlan.rootClass_eq_quote_of_static_generatedQuote
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rootStatic : plan.isStaticRoot = true)
    {arguments : List Pattern}
    (shape : pattern = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor arguments) :
    plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      simp only [CostStaticRegionPlan.rootClass]
      apply congrArg CostStaticPlanRootClass.application
      apply CostStaticColor.symbols_constructor_injective rhoCIGSLT color
      have wireEq := Pattern.apply.inj shape |>.1
      rw [← preimage.labelMap,
        rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered, wireEq]
      cases color <;> rfl
  | collection =>
      cases shape
  | bvar | fvar | boundaryApplication | lambda | multiLambda |
      boundaryCollection =>
      simp [CostStaticRegionPlan.isStaticRoot] at rootStatic

/-- The static plan exposed by a tree at the payload of a reached Quote has
the same authored Quote root class. -/
theorem CostStaticPlanReached.staticRootView_rootClass_eq_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType))
    (view : tree.StaticRootView color) :
    view.node.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
  obtain ⟨arguments, payloadEq⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote reached
      quoteRoot
  apply CostStaticRegionPlan.rootClass_eq_quote_of_static_generatedQuote
    view.node.plan view.node.rootStatic
  exact view.patternEq.trans payloadEq

/-- Occurrence-index transport leaves the normalized child at a fixed finite
position unchanged. -/
theorem CostRegionBoundaryTrees.castOccurrences_getEntry_normal
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (occurrencesEq : smallOccurrences = largeOccurrences)
    (position : Fin table.entries.length)
    (normalizeStatic : CostStaticRegionNormalizer source) :
    (((trees.castOccurrences occurrencesEq).getEntry
        (Fin.cast (by simp) position)).tree.normalize
          (normalizeStatic := normalizeStatic)).pattern =
      ((trees.getEntry position).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  cases occurrencesEq
  rfl

/-- Positional forests over two sealed Quote-root plans satisfy the normalized
availability suffix whenever corresponding boundary contents normalize alike. -/
theorem CostRegionBoundaryTrees.normalizedAvailabilitySuffixAcross_of_quoteRoots
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning rhoCIGSLT color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning rhoCIGSLT color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {smallSourceType largeSourceType : TypeExpr}
    (smallPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      smallSourceBound smallTargetBound smallThinning smallAvailable outer
      pattern smallSourceType)
    (largePlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      largeSourceBound largeTargetBound largeThinning largeAvailable outer
      pattern largeSourceType)
    {sealed : List TypeExpr}
    (aligned : CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed
      .sealed smallPlan largePlan)
    (smallQuote : smallPlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (largeQuote : largePlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallPlan.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable) :
    CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer sealed smallPlan.boundaryTable
        largePlan.boundaryTable smallTrees largeTrees := by
  have tables : TypedCostRegionBoundaryTable.AvailabilitySuffix sealed
      (TypedCostRegionBoundaryTable.cast aligned.occurrences_eq
        smallPlan.boundaryTable) largePlan.boundaryTable := by
    apply TypedCostRegionBoundaryTable.AvailabilitySuffix.of_certify
      aligned.fibers
    · rw [TypedCostRegionBoundaryTable.certify?_cast,
        smallPlan.certify_boundaryFibers]
      rfl
    · exact largePlan.certify_boundaryFibers
  apply CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross.of_getEntry_normal_eq
    aligned.occurrences_eq tables
  intro smallPosition largePosition positionEq
  let castSmallPosition : Fin
      (TypedCostRegionBoundaryTable.cast aligned.occurrences_eq
        smallPlan.boundaryTable).entries.length :=
    Fin.cast (by simp) smallPosition
  have castPositionEq : castSmallPosition.1 = largePosition.1 := by
    simpa [castSmallPosition] using positionEq
  have smallFrameFree : WellSorted.ReflectiveSubstitutionBinderFree
      smallPlan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      smallPlan
      ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot smallPlan
        smallQuote⟩
  have largeFrameFree : WellSorted.ReflectiveSubstitutionBinderFree
      largePlan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      largePlan
      ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot largePlan
        largeQuote⟩
  have smallSupportNil :
      (smallPlan.boundaryTable.entries.get smallPosition).boundary.targetSupport =
        [] :=
    CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot smallPlan
      smallFrameFree _ (List.get_mem _ _) smallQuote
  have largeSupportNil :
      (largePlan.boundaryTable.entries.get largePosition).boundary.targetSupport =
        [] :=
    CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot largePlan
      largeFrameFree _ (List.get_mem _ _) largeQuote
  have normalEq :=
    CostRegionBoundaryTrees.getEntry_normal_eq_of_availabilitySuffix
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      tables
      (smallTrees.castOccurrences aligned.occurrences_eq) largeTrees
      castSmallPosition largePosition castPositionEq (by
        simpa [castSmallPosition] using smallSupportNil.trans
          largeSupportNil.symm)
  exact (CostRegionBoundaryTrees.castOccurrences_getEntry_normal smallTrees
    aligned.occurrences_eq smallPosition rhoHereditaryStaticNormalizer).symm.trans
      normalEq

/-- Restrict a parent forest to a reached Quote plan and relate it
positionally to any visible static-root forest for the same payload. -/
theorem CostStaticPlanReached.exists_parentRestrictedQuoteForestAlignment
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (parentTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      parentNode.boundaryTable)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries
      parentNode.plan.boundaryTable.entries)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType))
    (view : tree.StaticRootView color) :
    let largePlan :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
        view.patternEq.symm
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostRegionTree.StaticRootView.sourceType_eq
            view).symm
          (reached.plan.recontextualize .hole)
    ∃ (sealed : List TypeExpr)
        (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
          largePlan.boundaryTable),
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
          view.node.plan largePlan ∧
        CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
          rhoHereditaryStaticNormalizer sealed view.node.boundaryTable
            largePlan.boundaryTable view.children largeTrees := by
  dsimp only
  let largePlan :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      view.patternEq.symm
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostRegionTree.StaticRootView.sourceType_eq
          view).symm
        (reached.plan.recontextualize .hole)
  have largeEntriesEq : largePlan.boundaryTable.entries =
      reached.plan.boundaryTable.entries := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries]
    exact reached.plan.recontextualizeEntriesEq .hole
  let largeEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      largePlan.boundaryTable.entries parentNode.plan.boundaryTable.entries :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanEntryEmbedding.castSource
      largeEntriesEq.symm embedding
  let largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding largePlan.boundaryTable
      parentNode.boundaryTable largeEmbedding parentTrees
  obtain ⟨sealed, aligned, _entriesEq, _abstractEq⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.staticRootView_boundaryFibersAvailabilitySuffix
      reached admission tree view
  have smallQuote :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.staticRootView_rootClass_eq_quoteRoot
      reached quoteRoot tree view
  have largeQuote : largePlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
    simp [largePlan, quoteRoot]
  have forests :=
    CostRegionBoundaryTrees.normalizedAvailabilitySuffixAcross_of_quoteRoots
      view.node.plan largePlan aligned smallQuote largeQuote view.children
        largeTrees
  exact ⟨sealed, largeTrees, aligned, forests⟩

/-- Build the existing semantic-atom environment for an arbitrary admitted
static plan and a proof-relevant boundary forest over its exact table. -/
noncomputable def CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    (trees : CostRegionBoundaryTrees source targetFree color
      plan.boundaryTable)
    (kernel : CostStaticNormalizationKernel source) :
    CostStaticAtomEnvironment.Packed source color targetFree
      plan.boundaryTable
      (trees.normalizeValues (normalizeStatic := kernel.normalize))
      plan.abstractPattern := by
  let values := trees.normalizeValues (normalizeStatic := kernel.normalize)
  let supportedSafe :=
    plan.abstractPattern_supportedSafe plan.boundaryTable (by
      intro boundary membership
      exact membership)
  let supported := Classical.choose supportedSafe
  let result := CostStaticAtomEnvironment.build? plan.boundaryTable values
    plan.abstractPattern
  have total : result.isSome = true := by
    exact CostStaticAtomEnvironment.build?_isSome_of_typed
      plan.boundaryTable values supported.toHasType
        (plan.abstractPattern_object payloadObject)
  exact result.get total

/-- The plan-indexed semantic environment is the same executable builder as
the canonical node repackaged from that plan. -/
theorem CostStaticRegionNode.semanticAtomEnvironmentOfTrees_eq_ofPlan
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (trees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.boundaryTable) :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        node.plan node.term.2.2.2.1 trees rhoHereditaryNormalizationKernel) =
      (CostStaticRegionNode.ofPlan node.term node.plan node.rootStatic
        ).semanticAtomEnvironment
        (trees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)) := by
  unfold
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
    CostStaticRegionNode.semanticAtomEnvironment
    CostStaticRegionNode.buildSemanticAtomEnvironment?
  rfl

/-- Semantic-atom reification changes free-variable names only, so it
preserves every constructor-fragment certificate. -/
theorem CostStaticAtomEnvironment.constructorsWithin_reify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (allowed : String → Prop) :
    ∀ pattern, ConstructorsWithin allowed pattern →
      ConstructorsWithin allowed (environment.reify pattern) := by
  intro pattern supported
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      simp [Pattern.renameFVars]
  | hfvar name =>
      simp [Pattern.renameFVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify, ConstructorsWithin]
        at supported ⊢
      refine ⟨supported.1, ?_⟩
      rw [constructorListWithin_iff_forall]
      intro reifiedArgument reifiedMembership
      rw [List.mem_map] at reifiedMembership
      obtain ⟨argument, membership, rfl⟩ := reifiedMembership
      exact inductionHypothesis argument membership
        ((constructorListWithin_iff_forall arguments).mp supported.2 argument
          membership)
  | hlambda binder body inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify, ConstructorsWithin] at ⊢
      exact inductionHypothesis supported
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify, ConstructorsWithin] at ⊢
      exact inductionHypothesis supported
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [CostStaticAtomEnvironment.reify, ConstructorsWithin]
        at supported ⊢
      exact ⟨bodyInduction supported.1, replacementInduction supported.2⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [CostStaticAtomEnvironment.reify, ConstructorsWithin]
        at supported ⊢
      rw [constructorListWithin_iff_forall]
      intro reifiedElement reifiedMembership
      rw [List.mem_map] at reifiedMembership
      obtain ⟨element, membership, rfl⟩ := reifiedMembership
      exact inductionHypothesis element membership
        ((constructorListWithin_iff_forall elements).mp supported element
          membership)

/-- Reifying a plan abstract from its positionally restricted child forest
and from the embedding parent forest preserves the restoration meaning of
every occurrence.  The ambient suffix is empty because restriction changes
the finite table, not the binder context. -/
noncomputable def CostStaticRegionPlan.restrictedReificationAligned
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rootTable)
    {root : Pattern}
    {rootInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rootTable
      (rootTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) root}
    (rootEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rootInventory)
    (liftOccurrence : CostStaticFVarOccurrence plan.abstractPattern →
      CostStaticFVarOccurrence root)
    (liftName : ∀ occurrence,
      (liftOccurrence occurrence).name = occurrence.name)
    (regime : CostStaticAvailabilityRegime) :
    let restrictedTrees :=
      CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees
    let packed :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
    let restrictedEnvironment :=
      CostStaticAtomEnvironment.ofInventory packed.1
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.reflection.1
      restrictedEnvironment.restorationSupport
      restrictedEnvironment.restorationAssignment
      rootEnvironment.restorationSupport
      rootEnvironment.restorationAssignment [] regime
      (restrictedEnvironment.reify plan.abstractPattern)
      (rootEnvironment.reify plan.abstractPattern) := by
  dsimp only
  let restrictedTrees :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding
      plan.boundaryTable rootTable embedding rootTrees
  let packed :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
      plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
  let restrictedEnvironment :=
    CostStaticAtomEnvironment.ofInventory packed.1
  rw [restrictedEnvironment.reify_eq_renameFVars,
    rootEnvironment.reify_eq_renameFVars]
  apply
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.renameFVars
  intro occurrence
  obtain ⟨restrictedSlot, restrictedSelected⟩ := Option.isSome_iff_exists.mp
    (restrictedEnvironment.slotOfName?_isSome_of_occurrence occurrence)
  let rootOccurrence := liftOccurrence occurrence
  obtain ⟨rootSlot, rootSelected⟩ := Option.isSome_iff_exists.mp
    (rootEnvironment.slotOfName?_isSome_of_occurrence rootOccurrence)
  have rootSelectedName : rootEnvironment.slotOfName? occurrence.name =
      some rootSlot := by
    rw [← liftName occurrence]
    exact rootSelected
  have resolveDefined
      (decoded : decodeCostRegionSourceVariableName occurrence.name = none) :
      plan.boundaryTable.resolve occurrence.name ≠ none := by
    have localSubset : plan.boundaryTable.entries ⊆
        plan.boundaryTable.entries := fun _ membership => membership
    obtain ⟨supported, _safe⟩ :=
      plan.abstractPattern_supportedSafe plan.boundaryTable localSubset
    obtain ⟨freeType, typedName⟩ :=
      supported.toHasType.freeType_of_mem_freeFvarNames_of_isObjectPattern
        (plan.abstractPattern_object payloadObject)
        occurrence.name_mem_freeFvarNames
    intro resolution
    simp [TypedCostRegionBoundaryTable.sourceFreeContext, decoded,
      resolution] at typedName
  have supportEq :
      (restrictedEnvironment.atomValue restrictedSlot).key.targetSupport =
        (rootEnvironment.atomValue rootSlot).key.targetSupport := by
    rw [restrictedEnvironment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
      occurrence restrictedSlot restrictedSelected]
    rw [rootEnvironment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
      rootOccurrence rootSlot rootSelected]
    rw [liftName occurrence]
    cases decoded : decodeCostRegionSourceVariableName occurrence.name with
    | some sourceName =>
        simp [TypedCostRegionBoundaryTable.restorationSupport, decoded]
    | none =>
        have tableResolution := plan.boundaryTable.resolve_eq_of_entries_subset
          rootTable embedding.subset occurrence.name (resolveDefined decoded)
        simp [TypedCostRegionBoundaryTable.restorationSupport, decoded,
          tableResolution]
  have normalEq :
      (restrictedEnvironment.atomValue restrictedSlot).key.normal =
        (rootEnvironment.atomValue rootSlot).key.normal := by
    rw [restrictedEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      occurrence restrictedSlot restrictedSelected]
    rw [rootEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rootOccurrence rootSlot rootSelected]
    change
      (restrictedTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            plan.boundaryTable occurrence.name =
        (rootTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            rootTable rootOccurrence.name
    rw [liftName occurrence]
    cases decoded : decodeCostRegionSourceVariableName occurrence.name with
    | some sourceName =>
        simp [TypedCostRegionBoundaryTable.Values.assignment, decoded]
    | none =>
        exact
          CostRegionBoundaryTrees.normalizeValues_assignment_restrict_eq_of_resolve_defined
            (kernel := rhoHereditaryNormalizationKernel)
            CostCanonicalLaws.rho_unambiguousStaticDecomposition
            plan.boundaryTable rootTable embedding rootTrees occurrence.name
              (resolveDefined decoded)
  let occurrenceRegime :=
    CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1 regime
      occurrence.context
  have supportAt : CostStaticAvailabilityAt [] occurrenceRegime
      (restrictedEnvironment.atomValue restrictedSlot).key.targetSupport
      (rootEnvironment.atomValue rootSlot).key.targetSupport := by
    cases occurrenceRegime <;> simp [CostStaticAvailabilityAt, supportEq]
  have reexposes : occurrenceRegime = .sealed →
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
        rhoCIGSLT.reflection.1 restrictedEnvironment.restorationSupport
        restrictedEnvironment.restorationAssignment
        rootEnvironment.restorationSupport
        rootEnvironment.restorationAssignment [] .exposed
        (.fvar (restrictedEnvironment.atomName restrictedSlot))
        (.fvar (rootEnvironment.atomName rootSlot)) := by
    intro _sealed depth
    simp only [ReflectiveContextSupport.substituteAt,
      CostStaticAvailabilityRegime.largeDepth]
    simp only [CostStaticAtomEnvironment.restorationSupport_atomName,
      CostStaticAtomEnvironment.restorationAssignment_atomName]
    rw [supportEq, normalEq]
    simp
  have aligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.atomNamesAt
      (profile := rhoCIGSLT.reflection.1) restrictedEnvironment rootEnvironment
      restrictedSlot rootSlot supportAt normalEq reexposes
  simpa [restrictedEnvironment, rootOccurrence,
    CostStaticAtomEnvironment.reifyName, restrictedSelected, rootSelectedName,
    liftName occurrence] using aligned

/-- Reifying a Quote-root plan from its restricted child forest and from an
embedding parent forest gives the same occurrence-wise restoration meaning.
The comparison retains the exact occurrence lift into the parent inventory. -/
noncomputable def CostStaticRegionPlan.restrictedQuoteReificationAligned
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    (quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rootTable)
    {root : Pattern}
    {rootInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rootTable
      (rootTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) root}
    (rootEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rootInventory)
    (liftOccurrence : CostStaticFVarOccurrence plan.abstractPattern →
      CostStaticFVarOccurrence root)
    (liftName : ∀ occurrence,
      (liftOccurrence occurrence).name = occurrence.name)
    (regime : CostStaticAvailabilityRegime) :
    let restrictedTrees :=
      CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees
    let packed :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
    let restrictedEnvironment :=
      CostStaticAtomEnvironment.ofInventory packed.1
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.reflection.1
      restrictedEnvironment.restorationSupport
      restrictedEnvironment.restorationAssignment
      rootEnvironment.restorationSupport
      rootEnvironment.restorationAssignment [] regime
      (restrictedEnvironment.reify plan.abstractPattern)
      (rootEnvironment.reify plan.abstractPattern) := by
  dsimp only
  let restrictedTrees :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding
      plan.boundaryTable rootTable embedding rootTrees
  let packed :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
      plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
  let restrictedEnvironment :=
    CostStaticAtomEnvironment.ofInventory packed.1
  rw [restrictedEnvironment.reify_eq_renameFVars,
    rootEnvironment.reify_eq_renameFVars]
  apply
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.renameFVars
  intro occurrence
  obtain ⟨restrictedSlot, restrictedSelected⟩ := Option.isSome_iff_exists.mp
    (restrictedEnvironment.slotOfName?_isSome_of_occurrence occurrence)
  let rootOccurrence := liftOccurrence occurrence
  obtain ⟨rootSlot, rootSelected⟩ := Option.isSome_iff_exists.mp
    (rootEnvironment.slotOfName?_isSome_of_occurrence rootOccurrence)
  have rootSelectedName : rootEnvironment.slotOfName? occurrence.name =
      some rootSlot := by
    rw [← liftName occurrence]
    exact rootSelected
  have restrictedSupport :
      (restrictedEnvironment.atomValue restrictedSlot).key.targetSupport =
        [] := by
    exact CostStaticRegionPlan.ofInventory_atomValue_targetSupport_eq_nil_of_quoteRoot
      plan
      (CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
        plan ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot
          plan quoteRoot⟩)
      quoteRoot packed.1 restrictedSlot
  have normalEq :
      (restrictedEnvironment.atomValue restrictedSlot).key.normal =
        (rootEnvironment.atomValue rootSlot).key.normal := by
    rw [restrictedEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      occurrence restrictedSlot restrictedSelected]
    rw [rootEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rootOccurrence rootSlot rootSelected]
    change
      (restrictedTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            plan.boundaryTable occurrence.name =
        (rootTrees.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer)).assignment
            rootTable rootOccurrence.name
    rw [liftName occurrence]
    cases decoded : decodeCostRegionSourceVariableName occurrence.name with
    | some sourceName =>
        simp [TypedCostRegionBoundaryTable.Values.assignment, decoded]
    | none =>
        have localSubset : plan.boundaryTable.entries ⊆
            plan.boundaryTable.entries := fun _ membership => membership
        obtain ⟨supported, _safe⟩ :=
          plan.abstractPattern_supportedSafe plan.boundaryTable localSubset
        obtain ⟨freeType, typedName⟩ :=
          supported.toHasType.freeType_of_mem_freeFvarNames_of_isObjectPattern
            (plan.abstractPattern_object payloadObject)
            occurrence.name_mem_freeFvarNames
        have defined : plan.boundaryTable.resolve occurrence.name ≠ none := by
          intro resolution
          simp [TypedCostRegionBoundaryTable.sourceFreeContext, decoded,
            resolution] at typedName
        exact
          CostRegionBoundaryTrees.normalizeValues_assignment_restrict_eq_of_resolve_defined
            (kernel := rhoHereditaryNormalizationKernel)
            CostCanonicalLaws.rho_unambiguousStaticDecomposition
            plan.boundaryTable rootTable embedding rootTrees occurrence.name
              defined
  simpa [restrictedEnvironment, rootOccurrence,
    CostStaticAtomEnvironment.reifyName, restrictedSelected, rootSelectedName,
    liftName occurrence] using
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.atomNamesAt_of_smallTargetSupport_nil
        (profile := rhoCIGSLT.reflection.1) (ambient := [])
          restrictedEnvironment rootEnvironment
          (CostStaticAvailabilityRegime.atContext rhoCIGSLT.reflection.1
            regime occurrence.context)
          restrictedSlot rootSlot restrictedSupport normalEq

/-- Positionally restricted and parent environments produce
restoration-related target canonical frames at every ambient depth. -/
noncomputable def CostStaticRegionPlan.restrictedCanonicalRestoresTogether
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rootTable)
    {root : Pattern}
    {rootInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rootTable
      (rootTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) root}
    (rootEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rootInventory)
    (liftOccurrence : CostStaticFVarOccurrence plan.abstractPattern →
      CostStaticFVarOccurrence root)
    (liftName : ∀ occurrence,
      (liftOccurrence occurrence).name = occurrence.name)
    (keyDepth : Nat) :
    let restrictedTrees :=
      CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees
    let packed :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
    let restrictedEnvironment :=
      CostStaticAtomEnvironment.ofInventory packed.1
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
      rhoCIGSLT.costWholeReflectionProfile
      restrictedEnvironment.restorationSupport
      restrictedEnvironment.restorationAssignment
      rootEnvironment.restorationSupport
      rootEnvironment.restorationAssignment
      [] .exposed
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt restrictedEnvironment)
        declaration keyDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (restrictedEnvironment.reify plan.abstractPattern)))
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rootEnvironment)
        declaration keyDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rootEnvironment.reify plan.abstractPattern))) := by
  dsimp only
  let restrictedTrees :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding
      plan.boundaryTable rootTable embedding rootTrees
  let packed :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
      plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
  let restrictedEnvironment :=
    CostStaticAtomEnvironment.ofInventory packed.1
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have sourceAligned :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.restrictedReificationAligned
      plan payloadObject rootTable embedding rootTrees rootEnvironment
        liftOccurrence liftName .exposed
  have mappedAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.mapPattern
      (color.symbols rhoCIGSLT)
      (fun constructor =>
        reflectiveIsQuoteConstructor_mapCostStatic rhoCIGSLT color constructor)
      sourceAligned
  have quoteRecognized : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor =
        true := by
    unfold declaration
    rw [costStaticReflectivePresentationDecl_eq_map]
    simp only [mapReflectivePresentation,
      CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
    simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]
  have sourceSupported : ConstructorsWithin (fun _ => True)
      (restrictedEnvironment.reify plan.abstractPattern) := by
    obtain ⟨typed, _safe⟩ :=
      plan.abstractPattern_supportedSafe plan.boundaryTable
        (fun _ membership => membership)
    apply
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticAtomEnvironment.constructorsWithin_reify
        restrictedEnvironment (fun _ => True) plan.abstractPattern
    exact typed.constructorsWithin.mono (fun _ _ => trivial)
  have targetSupported : ConstructorsWithin
      (fun constructor =>
        ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile constructor = true ↔
          constructor = declaration.quoteConstructor)
      (mapPattern (color.symbols rhoCIGSLT)
        (restrictedEnvironment.reify plan.abstractPattern)) := by
    apply constructorsWithin_mapPattern (color.symbols rhoCIGSLT)
    · intro constructor _supported
      rw [reflectiveIsQuoteConstructor_mapCostStatic]
      rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
      unfold declaration
      rw [costStaticReflectivePresentationDecl_eq_map]
      simp only [mapReflectivePresentation,
        CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
      constructor
      · intro recognized
        apply congrArg (color.symbols rhoCIGSLT).constructor
        have reversed : rhoReflectivePresentation.quoteConstructor =
            constructor := by
          simpa [ReflectiveContextSupport.isQuoteConstructor,
            rhoReflectionProfile] using recognized
        exact reversed.symm
      · intro equality
        have sourceEq : constructor =
            rhoReflectivePresentation.quoteConstructor :=
          CostStaticColor.symbols_constructor_injective rhoCIGSLT color
            equality
        subst constructor
        simp [ReflectiveContextSupport.isQuoteConstructor,
          rhoReflectionProfile]
    · exact sourceSupported
  have canonicalAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.canonicalizeByAt
      mappedAligned declaration quoteRecognized targetSupported keyDepth
  change ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
    rhoCIGSLT.costWholeReflectionProfile
    restrictedEnvironment.restorationSupport
    restrictedEnvironment.restorationAssignment
    rootEnvironment.restorationSupport rootEnvironment.restorationAssignment
    [] .exposed
    (canonicalizeByAt
      (fun current pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            restrictedEnvironment.restorationSupport
            restrictedEnvironment.restorationAssignment current pattern))
      declaration keyDepth
      (mapPattern (color.symbols rhoCIGSLT)
        (restrictedEnvironment.reify plan.abstractPattern)))
    (canonicalizeByAt
      (fun current pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            rootEnvironment.restorationSupport
            rootEnvironment.restorationAssignment current pattern))
      declaration keyDepth
      (mapPattern (color.symbols rhoCIGSLT)
        (rootEnvironment.reify plan.abstractPattern)))
  simpa [CostStaticAvailabilityRegime.largeDepth] using
      canonicalAligned.toRestoresTogether

/-- Positional restriction remains restoration-invariant after a common
binder thinning and selected-colour keyed canonicalization. -/
noncomputable def CostStaticRegionPlan.restrictedThickenedCanonicalRestoresTogether
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound frameSourceBound frameTargetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    (frameThinning : CostStaticBinderThinning rhoCIGSLT color frameSourceBound
      frameTargetBound)
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rootTable)
    {root : Pattern}
    {rootInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rootTable
      (rootTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) root}
    (rootEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rootInventory)
    (liftOccurrence : CostStaticFVarOccurrence plan.abstractPattern →
      CostStaticFVarOccurrence root)
    (liftName : ∀ occurrence,
      (liftOccurrence occurrence).name = occurrence.name)
    (scopeDepth keyDepth : Nat) :
    let restrictedTrees :=
      CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees
    let packed :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
    let restrictedEnvironment :=
      CostStaticAtomEnvironment.ofInventory packed.1
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
      rhoCIGSLT.costWholeReflectionProfile
      restrictedEnvironment.restorationSupport
      restrictedEnvironment.restorationAssignment
      rootEnvironment.restorationSupport
      rootEnvironment.restorationAssignment [] .exposed
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt restrictedEnvironment)
        declaration keyDepth
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (restrictedEnvironment.reify plan.abstractPattern))))
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rootEnvironment)
        declaration keyDepth
        (frameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rootEnvironment.reify plan.abstractPattern)))) := by
  dsimp only
  let restrictedTrees :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding
      plan.boundaryTable rootTable embedding rootTrees
  let packed :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
      plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
  let restrictedEnvironment :=
    CostStaticAtomEnvironment.ofInventory packed.1
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have sourceAligned :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.restrictedReificationAligned
      plan payloadObject rootTable embedding rootTrees rootEnvironment
        liftOccurrence liftName .exposed
  have mappedAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.mapPattern
      (color.symbols rhoCIGSLT)
      (fun constructor =>
        reflectiveIsQuoteConstructor_mapCostStatic rhoCIGSLT color constructor)
      sourceAligned
  have thickenedAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.thickenAmbientBVars
      frameThinning scopeDepth mappedAligned
  have quoteRecognized : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor =
        true := by
    unfold declaration
    rw [costStaticReflectivePresentationDecl_eq_map]
    simp only [mapReflectivePresentation,
      CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
    simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]
  have sourceSupported : ConstructorsWithin (fun _ => True)
      (restrictedEnvironment.reify plan.abstractPattern) := by
    obtain ⟨typed, _safe⟩ :=
      plan.abstractPattern_supportedSafe plan.boundaryTable
        (fun _ membership => membership)
    apply
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticAtomEnvironment.constructorsWithin_reify
        restrictedEnvironment (fun _ => True) plan.abstractPattern
    exact typed.constructorsWithin.mono (fun _ _ => trivial)
  have mappedSupported : ConstructorsWithin
      (fun constructor =>
        ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile constructor = true ↔
          constructor = declaration.quoteConstructor)
      (mapPattern (color.symbols rhoCIGSLT)
        (restrictedEnvironment.reify plan.abstractPattern)) := by
    apply constructorsWithin_mapPattern (color.symbols rhoCIGSLT)
    · intro constructor _supported
      rw [reflectiveIsQuoteConstructor_mapCostStatic]
      rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
      unfold declaration
      rw [costStaticReflectivePresentationDecl_eq_map]
      simp only [mapReflectivePresentation,
        CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
      constructor
      · intro recognized
        apply congrArg (color.symbols rhoCIGSLT).constructor
        have reversed : rhoReflectivePresentation.quoteConstructor =
            constructor := by
          simpa [ReflectiveContextSupport.isQuoteConstructor,
            rhoReflectionProfile] using recognized
        exact reversed.symm
      · intro equality
        have sourceEq : constructor =
            rhoReflectivePresentation.quoteConstructor :=
          CostStaticColor.symbols_constructor_injective rhoCIGSLT color
            equality
        subst constructor
        simp [ReflectiveContextSupport.isQuoteConstructor,
          rhoReflectionProfile]
    · exact sourceSupported
  have targetSupported :=
    frameThinning.constructorsWithin_thickenAmbientBVars mappedSupported
      scopeDepth
  have canonicalAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.canonicalizeByAt
      thickenedAligned declaration quoteRecognized targetSupported keyDepth
  change ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
    rhoCIGSLT.costWholeReflectionProfile
    restrictedEnvironment.restorationSupport
    restrictedEnvironment.restorationAssignment
    rootEnvironment.restorationSupport rootEnvironment.restorationAssignment
    [] .exposed
    (canonicalizeByAt
      (fun current pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            restrictedEnvironment.restorationSupport
            restrictedEnvironment.restorationAssignment current pattern))
      declaration keyDepth
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (restrictedEnvironment.reify plan.abstractPattern))))
    (canonicalizeByAt
      (fun current pattern =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            rootEnvironment.restorationSupport
            rootEnvironment.restorationAssignment current pattern))
      declaration keyDepth
      (frameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rootEnvironment.reify plan.abstractPattern))))
  simpa [CostStaticAvailabilityRegime.largeDepth] using
    canonicalAligned.toRestoresTogether

/-- Authored-Quote specialization of
`CostStaticRegionPlan.restrictedCanonicalRestoresTogether`. -/
noncomputable def CostStaticRegionPlan.restrictedQuoteCanonicalRestoresTogether
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    (_quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rootTable)
    {root : Pattern}
    {rootInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rootTable
      (rootTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer)) root}
    (rootEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rootInventory)
    (liftOccurrence : CostStaticFVarOccurrence plan.abstractPattern →
      CostStaticFVarOccurrence root)
    (liftName : ∀ occurrence,
      (liftOccurrence occurrence).name = occurrence.name) :
    let restrictedTrees :=
      CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees
    let packed :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
        plan payloadObject restrictedTrees rhoHereditaryNormalizationKernel
    let restrictedEnvironment :=
      CostStaticAtomEnvironment.ofInventory packed.1
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
      rhoCIGSLT.costWholeReflectionProfile
      restrictedEnvironment.restorationSupport
      restrictedEnvironment.restorationAssignment
      rootEnvironment.restorationSupport
      rootEnvironment.restorationAssignment
      [] .exposed
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt restrictedEnvironment)
        declaration 0
        (mapPattern (color.symbols rhoCIGSLT)
          (restrictedEnvironment.reify plan.abstractPattern)))
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt rootEnvironment)
        declaration 0
        (mapPattern (color.symbols rhoCIGSLT)
          (rootEnvironment.reify plan.abstractPattern))) :=
  CostStaticRegionPlan.restrictedCanonicalRestoresTogether plan payloadObject
    rootTable embedding rootTrees rootEnvironment liftOccurrence liftName 0

/-- Normalized forests over a sealed Quote-plan suffix induce the exact
endpoint-local reification alignment.  The apparent re-exposure callback is
vacuous because every boundary selected below the small Quote has empty
target support. -/
noncomputable def CostStaticRegionPlan.quoteReificationAligned_of_normalizedSuffix
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning rhoCIGSLT color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning rhoCIGSLT color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {smallSourceType largeSourceType : TypeExpr}
    (smallPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      smallSourceBound smallTargetBound smallThinning smallAvailable outer
        pattern smallSourceType)
    (largePlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      largeSourceBound largeTargetBound largeThinning largeAvailable outer
        pattern largeSourceType)
    (payloadObject : WellSorted.isObjectPattern pattern = true)
    {ambient : List TypeExpr}
    (aligned : CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix ambient
      .sealed smallPlan largePlan)
    (smallQuote : smallPlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallPlan.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable)
    {smallInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      smallPlan.boundaryTable
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      smallPlan.abstractPattern}
    {largeInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      largePlan.boundaryTable
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      largePlan.abstractPattern}
    (smallEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      largeInventory)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallPlan.boundaryTable
        largePlan.boundaryTable smallTrees largeTrees) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      rhoCIGSLT.reflection.1
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient .sealed
      (smallEnvironment.reify smallPlan.abstractPattern)
      (largeEnvironment.reify largePlan.abstractPattern) := by
  apply CostStaticAbstractPatternAlignment.reifyAligned_of_normalizedBoundaryTrees
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition smallTrees largeTrees
      smallEnvironment largeEnvironment forests aligned.abstractPattern
      (smallPlan.abstractPattern_object payloadObject)
      (largePlan.abstractPattern_object payloadObject)
  intro _current smallPosition _largePosition _positionEq _sealed nonempty
  exact (nonempty
    (CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot smallPlan
      (CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
        smallPlan
        ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot
          smallPlan smallQuote⟩)
      _ (List.get_mem _ _) smallQuote)).elim

/-- The selected-color keyed canonicalizer preserves a sealed Quote-plan
suffix after the positional boundary forests have been normalized. -/
noncomputable def CostStaticRegionPlan.quoteCanonicalRestoresTogether_of_normalizedSuffix
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallSourceBound smallTargetBound largeSourceBound largeTargetBound :
      List TypeExpr}
    {smallThinning : CostStaticBinderThinning rhoCIGSLT color smallSourceBound
      smallTargetBound}
    {largeThinning : CostStaticBinderThinning rhoCIGSLT color largeSourceBound
      largeTargetBound}
    {smallAvailable largeAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {smallSourceType largeSourceType : TypeExpr}
    (smallPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      smallSourceBound smallTargetBound smallThinning smallAvailable outer
        pattern smallSourceType)
    (largePlan : CostStaticRegionPlan rhoCIGSLT color targetFree
      largeSourceBound largeTargetBound largeThinning largeAvailable outer
        pattern largeSourceType)
    (payloadObject : WellSorted.isObjectPattern pattern = true)
    {ambient : List TypeExpr}
    (aligned : CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix ambient
      .sealed smallPlan largePlan)
    (smallQuote : smallPlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (smallTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      smallPlan.boundaryTable)
    (largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable)
    {smallInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      smallPlan.boundaryTable
      (smallTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      smallPlan.abstractPattern}
    {largeInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      largePlan.boundaryTable
      (largeTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      largePlan.abstractPattern}
    (smallEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      largeInventory)
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      rhoHereditaryStaticNormalizer ambient smallPlan.boundaryTable
        largePlan.boundaryTable smallTrees largeTrees) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
      rhoCIGSLT.costWholeReflectionProfile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient .sealed
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt smallEnvironment)
        declaration 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify smallPlan.abstractPattern)))
      (canonicalizeByAt
        (CostStaticRegionNode.semanticPatternKeyAt largeEnvironment)
        declaration 0
        (mapPattern (color.symbols rhoCIGSLT)
          (largeEnvironment.reify largePlan.abstractPattern))) := by
  dsimp only
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation
  have sourceAligned :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.quoteReificationAligned_of_normalizedSuffix
      smallPlan largePlan payloadObject aligned smallQuote smallTrees largeTrees
        smallEnvironment largeEnvironment forests
  have mappedAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.mapPattern
      (color.symbols rhoCIGSLT)
      (fun constructor =>
        reflectiveIsQuoteConstructor_mapCostStatic rhoCIGSLT color constructor)
      sourceAligned
  have quoteRecognized : ReflectiveContextSupport.isQuoteConstructor
      rhoCIGSLT.costWholeReflectionProfile declaration.quoteConstructor =
        true := by
    unfold declaration
    rw [costStaticReflectivePresentationDecl_eq_map]
    simp only [mapReflectivePresentation,
      CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
    rw [reflectiveIsQuoteConstructor_mapCostStatic]
    rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
    simp [ReflectiveContextSupport.isQuoteConstructor, rhoReflectionProfile]
  have sourceSupported : ConstructorsWithin (fun _ => True)
      (smallEnvironment.reify smallPlan.abstractPattern) := by
    obtain ⟨typed, _safe⟩ :=
      smallPlan.abstractPattern_supportedSafe smallPlan.boundaryTable
        (fun _ membership => membership)
    apply
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticAtomEnvironment.constructorsWithin_reify
        smallEnvironment (fun _ => True) smallPlan.abstractPattern
    exact typed.constructorsWithin.mono (fun _ _ => trivial)
  have targetSupported : ConstructorsWithin
      (fun constructor =>
        ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile constructor = true ↔
          constructor = declaration.quoteConstructor)
      (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify smallPlan.abstractPattern)) := by
    apply constructorsWithin_mapPattern (color.symbols rhoCIGSLT)
    · intro constructor _supported
      rw [reflectiveIsQuoteConstructor_mapCostStatic]
      rw [show rhoCIGSLT.reflection.1 = rhoReflectionProfile from rfl]
      unfold declaration
      rw [costStaticReflectivePresentationDecl_eq_map]
      simp only [mapReflectivePresentation,
        CostStaticColor.reflectiveSymbols_toLanguageDefSymbolMap]
      constructor
      · intro recognized
        apply congrArg (color.symbols rhoCIGSLT).constructor
        have reversed : rhoReflectivePresentation.quoteConstructor =
            constructor := by
          simpa [ReflectiveContextSupport.isQuoteConstructor,
            rhoReflectionProfile] using recognized
        exact reversed.symm
      · intro equality
        have sourceEq : constructor =
            rhoReflectivePresentation.quoteConstructor :=
          CostStaticColor.symbols_constructor_injective rhoCIGSLT color
            equality
        subst constructor
        simp [ReflectiveContextSupport.isQuoteConstructor,
          rhoReflectionProfile]
    · exact sourceSupported
  have canonicalAligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.canonicalizeByAt
      mappedAligned declaration quoteRecognized targetSupported 0
  change ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
    rhoCIGSLT.costWholeReflectionProfile
    smallEnvironment.restorationSupport
    smallEnvironment.restorationAssignment
    largeEnvironment.restorationSupport
    largeEnvironment.restorationAssignment ambient .sealed
    (canonicalizeByAt
      (fun current candidate =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            smallEnvironment.restorationSupport
            smallEnvironment.restorationAssignment current candidate))
      declaration 0
      (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify smallPlan.abstractPattern)))
    (canonicalizeByAt
      (fun current candidate =>
        Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
          (ReflectiveContextSupport.substituteAt
            rhoCIGSLT.costWholeReflectionProfile
            largeEnvironment.restorationSupport
            largeEnvironment.restorationAssignment current candidate))
      declaration 0
      (mapPattern (color.symbols rhoCIGSLT)
        (largeEnvironment.reify largePlan.abstractPattern)))
  exact canonicalAligned.toRestoresTogether

/-- A reached authored Quote, interpreted in the enclosing static
environment, restores to the hereditary normal form of its payload tree. -/
noncomputable def CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (parentTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      parentNode.finiteBoundaryTable)
    {parentInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable
      (parentTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      parentNode.skeleton.1}
    (parentEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      parentInventory)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries
      parentNode.plan.boundaryTable.entries)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType))
    (availableDepth scopeDepth restorationDepth : Nat) :
    parentEnvironment.restoreAt restorationDepth
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                parentEnvironment)
              rhoReflectivePresentation availableDepth scopeDepth
              (parentEnvironment.reify reached.plan.abstractPattern)))) =
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  obtain ⟨view⟩ :=
    CostStaticPlanReached.nonempty_staticRootView_of_quoteRoot reached
      quoteRoot tree
  let largePlan := CostStaticRegionPlan.reindexPatternSourceType
    view.patternEq.symm
      (CostRegionTree.StaticRootView.sourceType_eq view).symm
      (reached.plan.recontextualize .hole)
  have largeEntriesEq : largePlan.boundaryTable.entries =
      reached.plan.boundaryTable.entries := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries]
    exact reached.plan.recontextualizeEntriesEq .hole
  let largeEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      largePlan.boundaryTable.entries parentNode.plan.boundaryTable.entries :=
    CostStaticPlanEntryEmbedding.castSource largeEntriesEq.symm embedding
  let largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding largePlan.boundaryTable
      parentNode.boundaryTable largeEmbedding parentTrees
  obtain ⟨_sealed, planAligned, _entriesEq, _abstractEq⟩ :=
    CostStaticPlanReached.staticRootView_boundaryFibersAvailabilitySuffix
      reached admission tree view
  have smallQuote :=
    CostStaticPlanReached.staticRootView_rootClass_eq_quoteRoot reached
      quoteRoot tree view
  have largeQuote : largePlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
    simp [largePlan, quoteRoot]
  have forestsAligned :=
    CostRegionBoundaryTrees.normalizedAvailabilitySuffixAcross_of_quoteRoots
      view.node.plan largePlan planAligned smallQuote largeQuote view.children
        largeTrees
  let reconstructedNode := CostStaticRegionNode.ofPlan
    view.node.term view.node.plan view.node.rootStatic
  let smallValues := view.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let smallPacked := reconstructedNode.semanticAtomEnvironment smallValues
  let smallInventory := smallPacked.1
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largePacked := CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
    largePlan view.node.term.2.2.2.1 largeTrees
      rhoHereditaryNormalizationKernel
  let largeInventory := largePacked.1
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have viewToRestricted :=
    CostStaticRegionPlan.quoteCanonicalRestoresTogether_of_normalizedSuffix
      view.node.plan largePlan view.node.term.2.2.2.1 planAligned smallQuote
        view.children largeTrees smallEnvironment largeEnvironment
          forestsAligned
  have largeAbstractEq : largePlan.abstractPattern =
      reached.plan.abstractPattern := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_abstractPattern]
    exact reached.plan.recontextualizeAbstractEq .hole
  have parentRootEq : parentNode.skeleton.1 =
      reached.skeletonContext.fill reached.plan.abstractPattern :=
    parentNode.skeleton_pattern.trans reached.abstract_eq
  let liftLargeOccurrence : CostStaticFVarOccurrence
      largePlan.abstractPattern → CostStaticFVarOccurrence
        parentNode.skeleton.1 := fun occurrence =>
    CostStaticFVarOccurrence.castRoot parentRootEq.symm
      ((CostStaticFVarOccurrence.castRoot largeAbstractEq occurrence).inContext
        reached.skeletonContext)
  have liftLargeName : ∀ occurrence,
      (liftLargeOccurrence occurrence).name = occurrence.name := by
    intro occurrence
    simp [liftLargeOccurrence]
  have largeToParent :=
    CostStaticRegionPlan.restrictedQuoteCanonicalRestoresTogether
      largePlan view.node.term.2.2.2.1 largeQuote parentNode.boundaryTable
        largeEmbedding parentTrees parentEnvironment liftLargeOccurrence
          liftLargeName
  let sourceCanonical := canonicalizeByDepths
    (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
      parentEnvironment)
    rhoReflectivePresentation availableDepth scopeDepth
    (parentEnvironment.reify reached.plan.abstractPattern)
  have sourceAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (parentEnvironment.reify reached.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      reached.plan quoteRoot
  have sourceCanonicalSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0 sourceCanonical = true := by
    exact canonicalizeByDepths_binderSafeAt
      (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
        parentEnvironment)
      rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
      availableDepth scopeDepth 0
      (parentEnvironment.reify reached.plan.abstractPattern)
      sourceAbstractSafe
  have mappedSourceCanonicalSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT) sourceCanonical) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      sourceCanonicalSafe
  let frame := parentNode.thinning.thickenAmbientBVars scopeDepth
    (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
  have frameEq : frame =
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical := by
    exact parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      scopeDepth (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
      mappedSourceCanonicalSafe
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun current _ candidate =>
      CostStaticRegionNode.semanticPatternKeyAt parentEnvironment current
        candidate
  have mappedAbstractSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT)
        (parentEnvironment.reify reached.plan.abstractPattern)) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      sourceAbstractSafe
  have sourceCanonicalEqExplicit : sourceCanonical =
      canonicalizeByDepths
        (fun current structural candidate =>
          CostStaticRegionNode.semanticPatternKeyAt parentEnvironment current
            (parentNode.thinning.thickenAmbientBVars structural
              (mapPattern (color.symbols rhoCIGSLT) candidate)))
        rhoReflectivePresentation availableDepth scopeDepth
        (parentEnvironment.reify reached.plan.abstractPattern) := by
    rfl
  have targetNaturality :
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
        canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    have naturality :=
      Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
        parentNode.thinning targetKey rhoReflectivePresentation
          availableDepth scopeDepth
          (parentEnvironment.reify reached.plan.abstractPattern)
    have inputThin :=
      parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern))
        mappedAbstractSafe
    have outputThin :=
      parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
        mappedSourceCanonicalSafe
    calc
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
          parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT) sourceCanonical) :=
        outputThin.symm
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (parentNode.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (parentEnvironment.reify
                  reached.plan.abstractPattern))) := by
        rw [sourceCanonicalEqExplicit]
        simpa [targetKey, targetDeclaration] using naturality
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (parentEnvironment.reify reached.plan.abstractPattern)) := by
        exact congrArg
          (canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth) inputThin
  have targetIgnoreScope :
      canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    simpa [targetKey] using
      canonicalizeByDepths_ignoreScope
        (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
        targetDeclaration availableDepth scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern))
  obtain ⟨quoteArguments, abstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot reached.plan
      quoteRoot
  have mappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (quoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (parentEnvironment.reify argument)) := by
    rw [abstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have targetQuoteDepthIndependent :
      canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    rw [mappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have targetCanonicalEq :
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify largePlan.abstractPattern)) := by
    rw [largeAbstractEq]
    exact targetNaturality.trans
      (targetIgnoreScope.trans targetQuoteDepthIndependent)
  let smallCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt smallEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (smallEnvironment.reify view.node.plan.abstractPattern))
  have smallSupportNil : ∀ slot,
      (smallEnvironment.atomValue slot).key.targetSupport = [] := by
    intro slot
    exact
      CostStaticRegionPlan.ofInventory_atomValue_targetSupport_eq_nil_of_quoteRoot
        view.node.plan
        (CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
          view.node.plan
          ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot
            view.node.plan smallQuote⟩)
        smallQuote smallInventory slot
  have smallAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (smallEnvironment.reify view.node.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      view.node.plan smallQuote
  have smallMappedAbstractSafe : binderSafeAt targetDeclaration.quoteConstructor
      0 (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify view.node.plan.abstractPattern)) = true := by
    have mapped : binderSafeAt
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor) 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern)) = true := by
      simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
        smallAbstractSafe
    simpa [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] using mapped
  have reconstructedTargetFrame :
      reconstructedNode.reifyTargetFrame smallEnvironment =
        mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern) := by
    rw [reconstructedNode.reifyTargetFrame_eq_map_reifiedSourceFrame
      smallEnvironment]
    exact
      reconstructedNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        targetDeclaration.quoteConstructor 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern))
        smallMappedAbstractSafe
  obtain ⟨smallQuoteArguments, smallAbstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot view.node.plan
      smallQuote
  have smallMappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (smallQuoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (smallEnvironment.reify argument)) := by
    rw [smallAbstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have smallCanonicalEqReconstructed : smallCanonical =
      reconstructedNode.canonicalizeReifiedTargetFrame smallEnvironment
        targetDeclaration := by
    unfold smallCanonical
    unfold CostStaticRegionNode.canonicalizeReifiedTargetFrame
    rw [reconstructedTargetFrame, smallMappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have smallRestoreDepth :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        smallEnvironment.restoreAt reconstructedNode.targetBound.length
          smallCanonical := by
    exact smallEnvironment.restoreAt_eq_of_atomTargetSupport_eq_nil
      smallSupportNil smallCanonical restorationDepth
        reconstructedNode.targetBound.length
  have smallRestoreEqNormalize :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (CostStaticRegionNode.normalizeHereditary reconstructedNode
          smallValues).1 := by
    rw [smallRestoreDepth, smallCanonicalEqReconstructed]
    rfl
  have reconstructedNormalizeEqTree :
      (CostStaticRegionNode.normalizeHereditary reconstructedNode
        smallValues).1 =
        (tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    let reconstructedTree : CostRegionTree rhoCIGSLT targetFree
        reached.sourceAvailable [] payload
        (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType) :=
      (((CostRegionTree.static (outer := []) reconstructedNode
          view.children).reindexPattern view.patternEq).reindexAvailable
            view.availableEq).reindexType view.typeEq
    let reconstructedView : reconstructedTree.StaticRootView color :=
      { node := reconstructedNode
        children := view.children
        patternEq := view.patternEq
        availableEq := view.availableEq
        typeEq := view.typeEq
        treeEq := rfl }
    have exposedNormal :=
      (reconstructedView.normalize_pattern rhoHereditaryStaticNormalizer).symm
    have treeNormal := CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel reconstructedTree tree admission.object
    exact exposedNormal.trans treeNormal
  have smallRestoreEqTree :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    smallRestoreEqNormalize.trans reconstructedNormalizeEqTree
  let largeCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt largeEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (largeEnvironment.reify largePlan.abstractPattern))
  let parentCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (parentEnvironment.reify largePlan.abstractPattern))
  have smallToParentRaw :=
    (viewToRestricted restorationDepth).trans
      (largeToParent restorationDepth)
  have parentCanonicalEqFrame : parentCanonical = frame := by
    exact targetCanonicalEq.symm.trans frameEq.symm
  change parentEnvironment.restoreAt restorationDepth frame = _
  rw [← parentCanonicalEqFrame]
  exact smallToParentRaw.symm.trans smallRestoreEqTree

/-- Every atom name in a reached source frame remains covered after source
canonicalization, colour mapping, and ambient-binder reinsertion. -/
theorem CostStaticPlanReached.parentCanonicalFrame_atomCovered
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (availableDepth scopeDepth : Nat) :
    environment.Covers
      (parentNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
              environment)
            rhoReflectivePresentation availableDepth scopeDepth
            (environment.reify reached.plan.abstractPattern)))) := by
  intro name membership
  have canonicalMembership : name ∈
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
          environment)
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern)).freeFvarNames := by
    simpa [CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
      StructuralMorphism.mapPattern_freeFvarNames] using membership
  have reachedMembership : name ∈
      (environment.reify reached.plan.abstractPattern).freeFvarNames :=
    (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
      (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode environment)
      rhoReflectivePresentation name availableDepth scopeDepth
      (environment.reify reached.plan.abstractPattern)).mp
        canonicalMembership
  let reify : Pattern → Pattern := fun pattern => environment.reify pattern
  have filledMembership : name ∈
      (reify (reached.skeletonContext.fill
        reached.plan.abstractPattern)).freeFvarNames := by
    change name ∈
      (environment.reify (reached.skeletonContext.fill
        reached.plan.abstractPattern)).freeFvarNames
    rw [← environment.reifyContext_fill]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      (environment.reifyContext reached.skeletonContext) reachedMembership
  have rootEq : parentNode.skeleton.1 =
      reached.skeletonContext.fill reached.plan.abstractPattern :=
    parentNode.skeleton_pattern.trans reached.abstract_eq
  have reifiedRootEq : reify parentNode.skeleton.1 =
      reify (reached.skeletonContext.fill reached.plan.abstractPattern) :=
    congrArg reify rootEq
  have rootMembership : name ∈
      (reify parentNode.skeleton.1).freeFvarNames := by
    rw [reifiedRootEq]
    exact filledMembership
  have targetMembership : name ∈
      (parentNode.reifyTargetFrame environment).freeFvarNames := by
    rw [parentNode.reifyTargetFrame_eq_map_reifiedSourceFrame]
    simpa [reify, CostStaticRegionNode.reifiedSourceFrame,
      CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
      StructuralMorphism.mapPattern_freeFvarNames] using rootMembership
  exact parentNode.reifyTargetFrame_atomCovered environment name
    targetMembership

/-- A certified boundary facing an admitted authored Quote reduces the exact
plan-stop source-alignment obligation to the recursively normalized payload
pair and the Quote plan's sealed positional forest. -/
noncomputable def boundaryQuotePlanStops_sourcePatternLeafAligned_withCospan_of_closeSmaller
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
    (cospan : CostStaticAtomKeyCospan
      (fun slot => (leftEnvironment.atomValue slot).key)
      (fun slot => (rightEnvironment.atomValue slot).key))
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftBoundary : leftReached.BoundaryView)
    (rightAdmission : rightReached.plan.RawAdmission)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightNode.term.1)
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
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (availableDepth scopeDepth : Nat) :
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
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftNode
          leftEnvironment)
        rhoReflectivePresentation availableDepth scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation availableDepth scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  intro relation
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftBoundary.stopped.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa only [leftBoundary.entries_eq] using leftEmbedding
  let leftAtRoot := leftBoundary.stopped.castRoot
    leftNode.skeleton_pattern.symm
  have castTyped : leftAtRoot.certified.typed =
      leftBoundary.stopped.certified.typed :=
    CostStaticPlanStopped.castRoot_certified_typed
      leftNode.skeleton_pattern.symm leftBoundary.stopped
  have leftEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftAtRoot.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    rw [castTyped]
    exact leftEmbedding'
  obtain ⟨leftSlot, leftSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence
      leftAtRoot.boundaryOccurrence)
  have leftSelectedBoundary : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        leftBoundary.stopped.certified.typed.boundary) = some leftSlot := by
    rw [← castTyped]
    exact leftSelectedAtRoot
  have contentEq : leftAtRoot.certified.typed.boundary.content =
      leftPayload := by
    rw [castTyped]
    exact leftBoundary.content_eq
  have targetSupportEq : leftAtRoot.certified.typed.boundary.targetSupport =
      rightReached.sourceAvailable := by
    rw [castTyped, leftBoundary.targetSupport_eq, sourceAvailableEq]
  have targetTypeEq : leftAtRoot.certified.typed.boundary.targetType =
      mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType := by
    rw [castTyped, leftBoundary.targetType_eq, sourceTypeEq]
  have leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType
      leftAtRoot.certified.typed.boundary.content := by
    exact ⟨⟨leftAtRoot.certified.typed.contentTyped,
          leftAtRoot.certified.typed.contentCanonicalBinderMetadata,
          leftAtRoot.certified.typed.contentObjectPattern,
          leftAtRoot.certified.typed.contentTyped.isWellScopedAt⟩,
        leftAtRoot.certified.typed.contentReflectiveScopeSafe⟩
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftAtRoot.certified.typed.boundary.targetSupport
      leftAtRoot.certified.typed.boundary.targetType rightPayload := by
    rw [targetSupportEq, targetTypeEq]
    exact rightAdmission.wellSorted
  have canonical : canonicalize childDeclaration
        leftAtRoot.certified.typed.boundary.content =
      canonicalize childDeclaration rightPayload := by
    rw [contentEq]
    exact rawAligned.canonicalize_eq childDeclaration stopCanonical
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries := leftEmbedding'.subset (by simp)
  have leftSmaller :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot
      leftNode.rootStatic leftBoundary.stopped.certified.typed leftMember
  have smaller :
      sizeOf leftAtRoot.certified.typed.boundary.content + sizeOf rightPayload <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
    rw [contentEq]
    have leftSize : sizeOf leftPayload < sizeOf leftNode.term.1 := by
      simpa only [leftBoundary.content_eq] using leftSmaller
    omega
  have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      leftAtRoot.certified.typed.boundary.targetType := by
    rw [targetTypeEq]
    exact rightEndpointAdmissible
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftWellSorted rightWellSorted canonical
      smaller leftAdmissible)
  let selectedTree := leftAtRoot.selectedTreeFromForest leftEmbeddingAtRoot
    leftTrees
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
  let rightTree : CostRegionTree rhoCIGSLT targetFree
      rightReached.sourceAvailable [] rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostRegionTree.reindexFiber targetSupportEq rfl targetTypeEq pair.rightTree
  have pairRightToTree :
      (pair.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    simp [rightTree]
  have leftAtom := leftAtRoot.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbeddingAtRoot
      leftTrees leftEnvironment leftSlot leftSelectedAtRoot
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      (rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have normalEq := congrArg (fun atom => atom.key.normal) leftAtom
    have atomToChild : (leftEnvironment.atomValue leftSlot).key.normal =
        ((leftAtRoot.selectedTreeFromForest leftEmbeddingAtRoot leftTrees
          ).normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
    rw [CostRegionTree.normalizedBoundaryValue_pattern] at atomToChild
    exact atomToChild.trans
      (by simpa only [selectedTree, rhoHereditaryNormalizationKernel] using
        (selectedToPair.trans pairNormal).trans pairRightToTree)
  obtain ⟨rightStaticView⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.nonempty_staticRootView_of_quoteRoot
      rightReached rightQuote rightTree
  let largePlan :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      rightStaticView.patternEq.symm
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostRegionTree.StaticRootView.sourceType_eq
          rightStaticView).symm
        (rightReached.plan.recontextualize .hole)
  have largeEntriesEq : largePlan.boundaryTable.entries =
      rightReached.plan.boundaryTable.entries := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries]
    exact rightReached.plan.recontextualizeEntriesEq .hole
  let largeEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      largePlan.boundaryTable.entries rightNode.plan.boundaryTable.entries :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanEntryEmbedding.castSource
      largeEntriesEq.symm rightEmbedding
  let largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding largePlan.boundaryTable
      rightNode.boundaryTable largeEmbedding rightTrees
  obtain ⟨sealed, planAligned, _entriesEq, _abstractEq⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.staticRootView_boundaryFibersAvailabilitySuffix
      rightReached rightAdmission rightTree rightStaticView
  have smallQuote :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.staticRootView_rootClass_eq_quoteRoot
      rightReached rightQuote rightTree rightStaticView
  have largeQuote : largePlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
    simp [largePlan, rightQuote]
  have forestsAligned :=
    CostRegionBoundaryTrees.normalizedAvailabilitySuffixAcross_of_quoteRoots
      rightStaticView.node.plan largePlan planAligned smallQuote largeQuote
        rightStaticView.children largeTrees
  let reconstructedNode := CostStaticRegionNode.ofPlan
    rightStaticView.node.term rightStaticView.node.plan
      rightStaticView.node.rootStatic
  let smallValues := rightStaticView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let smallPacked := reconstructedNode.semanticAtomEnvironment smallValues
  let smallInventory := smallPacked.1
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largePacked :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
      largePlan rightStaticView.node.term.2.2.2.1 largeTrees
        rhoHereditaryNormalizationKernel
  let largeInventory := largePacked.1
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have viewToRestricted :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.quoteCanonicalRestoresTogether_of_normalizedSuffix
      rightStaticView.node.plan largePlan
        rightStaticView.node.term.2.2.2.1 planAligned smallQuote
        rightStaticView.children largeTrees smallEnvironment largeEnvironment
          forestsAligned
  have largeAbstractEq : largePlan.abstractPattern =
      rightReached.plan.abstractPattern := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_abstractPattern]
    exact rightReached.plan.recontextualizeAbstractEq .hole
  have rightRootEq : rightNode.skeleton.1 =
      rightReached.skeletonContext.fill
        rightReached.plan.abstractPattern :=
    rightNode.skeleton_pattern.trans rightReached.abstract_eq
  let liftLargeOccurrence : CostStaticFVarOccurrence
      largePlan.abstractPattern → CostStaticFVarOccurrence
        rightNode.skeleton.1 := fun occurrence =>
    CostStaticFVarOccurrence.castRoot rightRootEq.symm
      ((CostStaticFVarOccurrence.castRoot largeAbstractEq occurrence).inContext
        rightReached.skeletonContext)
  have liftLargeName : ∀ occurrence,
      (liftLargeOccurrence occurrence).name = occurrence.name := by
    intro occurrence
    simp [liftLargeOccurrence]
  have largeToParent :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.restrictedQuoteCanonicalRestoresTogether
      largePlan rightStaticView.node.term.2.2.2.1 largeQuote
        rightNode.boundaryTable largeEmbedding rightTrees rightEnvironment
          liftLargeOccurrence liftLargeName
  rw [leftBoundary.abstract_eq]
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  unfold ReflectiveContextSupport.RestoresTogether
  intro restorationDepth
  simp only [mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars]
  have leftName : leftEnvironment.reifyName
      (costRegionBoundaryVariableName
        leftBoundary.stopped.certified.typed.boundary) =
      leftEnvironment.atomName leftSlot := by
    unfold CostStaticAtomEnvironment.reifyName
    rw [leftSelectedBoundary]
  rw [leftName]
  let rightFrame := rightNode.thinning.thickenAmbientBVars sourceDepth
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation availableDepth scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)))
  let rightReify : Pattern → Pattern := fun pattern =>
    CostStaticAtomEnvironment.reify (inventory := rightInventory)
      rightEnvironment pattern
  have leftCovered : ∀ name, name ∈ (Pattern.fvar
        (leftEnvironment.atomName leftSlot)).freeFvarNames →
      ∃ slot, leftEnvironment.lookupAtom? name = some slot := by
    intro name membership
    simp only [Pattern.freeFvarNames, List.mem_singleton] at membership
    subst name
    exact ⟨leftSlot, leftEnvironment.lookupAtom?_atomName leftSlot⟩
  have rightCovered : ∀ name, name ∈ rightFrame.freeFvarNames →
      ∃ slot, rightEnvironment.lookupAtom? name = some slot := by
    intro name membership
    have canonicalMembership : name ∈
        (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
            rightEnvironment)
          rhoReflectivePresentation availableDepth scopeDepth
          (rightEnvironment.reify
            rightReached.plan.abstractPattern)).freeFvarNames := by
      simpa [rightFrame,
        CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
        StructuralMorphism.mapPattern_freeFvarNames] using
          membership
    have reachedMembership : name ∈
        (rightEnvironment.reify
          rightReached.plan.abstractPattern).freeFvarNames :=
      (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation name availableDepth scopeDepth
        (rightEnvironment.reify
          rightReached.plan.abstractPattern)).mp canonicalMembership
    have filledMembership : name ∈
        (rightReify (rightReached.skeletonContext.fill
          rightReached.plan.abstractPattern)).freeFvarNames := by
      change name ∈
        (rightEnvironment.reify (rightReached.skeletonContext.fill
          rightReached.plan.abstractPattern)).freeFvarNames
      rw [← rightEnvironment.reifyContext_fill]
      exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
        (rightEnvironment.reifyContext rightReached.skeletonContext)
        reachedMembership
    have rootEq : rightNode.skeleton.1 =
        rightReached.skeletonContext.fill
          rightReached.plan.abstractPattern :=
      rightNode.skeleton_pattern.trans rightReached.abstract_eq
    have reifiedRootEq : rightReify rightNode.skeleton.1 =
        rightReify (rightReached.skeletonContext.fill
          rightReached.plan.abstractPattern) := congrArg rightReify rootEq
    have rootMembership : name ∈
        (rightReify rightNode.skeleton.1).freeFvarNames := by
      rw [reifiedRootEq]
      exact filledMembership
    have targetMembership : name ∈
        (rightNode.reifyTargetFrame rightEnvironment).freeFvarNames := by
      rw [rightNode.reifyTargetFrame_eq_map_reifiedSourceFrame]
      simpa [rightReify, CostStaticRegionNode.reifiedSourceFrame,
        CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
        StructuralMorphism.mapPattern_freeFvarNames] using
          rootMembership
    exact rightNode.reifyTargetFrame_atomCovered rightEnvironment name
      targetMembership
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
      restorationDepth (.fvar (leftEnvironment.atomName leftSlot))
      leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
      restorationDepth rightFrame rightCovered
  let rightCanonical := canonicalizeByDepths
    (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
      rightEnvironment)
    rhoReflectivePresentation availableDepth scopeDepth
    (rightEnvironment.reify rightReached.plan.abstractPattern)
  have rightAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (rightEnvironment.reify rightReached.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      rightReached.plan rightQuote
  have rightCanonicalSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0 rightCanonical = true := by
    exact canonicalizeByDepths_binderSafeAt
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
        rightEnvironment)
      rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
      availableDepth scopeDepth 0
      (rightEnvironment.reify rightReached.plan.abstractPattern)
      rightAbstractSafe
  have rightMappedCanonicalSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT) rightCanonical) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      rightCanonicalSafe
  have rightFrame_eq : rightFrame =
      mapPattern (color.symbols rhoCIGSLT) rightCanonical := by
    exact rightNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      sourceDepth (mapPattern (color.symbols rhoCIGSLT) rightCanonical)
      rightMappedCanonicalSafe
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun current _ candidate =>
      CostStaticRegionNode.semanticPatternKeyAt rightEnvironment current
        candidate
  have mappedAbstractSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT)
        (rightEnvironment.reify
          rightReached.plan.abstractPattern)) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      rightAbstractSafe
  have rightCanonical_eq_explicit : rightCanonical =
      canonicalizeByDepths
        (fun current structural candidate =>
          CostStaticRegionNode.semanticPatternKeyAt rightEnvironment current
            (rightNode.thinning.thickenAmbientBVars structural
              (mapPattern (color.symbols rhoCIGSLT) candidate)))
        rhoReflectivePresentation availableDepth scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern) := by
    rfl
  have targetNaturality :
      mapPattern (color.symbols rhoCIGSLT) rightCanonical =
        canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify
              rightReached.plan.abstractPattern)) := by
    have naturality :=
      Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
        rightNode.thinning
      targetKey rhoReflectivePresentation availableDepth scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)
    have inputThin :=
      rightNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightReached.plan.abstractPattern))
        mappedAbstractSafe
    have outputThin :=
      rightNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth (mapPattern (color.symbols rhoCIGSLT) rightCanonical)
        rightMappedCanonicalSafe
    calc
      mapPattern (color.symbols rhoCIGSLT) rightCanonical =
          rightNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT) rightCanonical) :=
        outputThin.symm
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (rightNode.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify
                  rightReached.plan.abstractPattern))) := by
        rw [rightCanonical_eq_explicit]
        simpa [targetKey, targetDeclaration] using naturality
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify
                rightReached.plan.abstractPattern)) := by
        exact congrArg
          (canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth) inputThin
  have targetIgnoreScope :
      canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify
              rightReached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify
              rightReached.plan.abstractPattern)) := by
    simpa [targetKey] using
      canonicalizeByDepths_ignoreScope
        (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
        targetDeclaration availableDepth scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightReached.plan.abstractPattern))
  obtain ⟨quoteArguments, rightAbstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot
      rightReached.plan rightQuote
  have rightMappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify rightReached.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (quoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify argument)) := by
    rw [rightAbstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have targetQuoteDepthIndependent :
      canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify
              rightReached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify
              rightReached.plan.abstractPattern)) := by
    rw [rightMappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have rightTargetCanonicalEq :
      mapPattern (color.symbols rhoCIGSLT) rightCanonical =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify largePlan.abstractPattern)) := by
    rw [largeAbstractEq]
    exact targetNaturality.trans
      (targetIgnoreScope.trans targetQuoteDepthIndependent)
  let smallCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt smallEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (smallEnvironment.reify rightStaticView.node.plan.abstractPattern))
  have smallSupportNil : ∀ slot,
      (smallEnvironment.atomValue slot).key.targetSupport = [] := by
    intro slot
    exact
      CostStaticRegionPlan.ofInventory_atomValue_targetSupport_eq_nil_of_quoteRoot
        rightStaticView.node.plan
        (CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
          rightStaticView.node.plan
          ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot
            rightStaticView.node.plan smallQuote⟩)
        smallQuote smallInventory slot
  have smallAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (smallEnvironment.reify
        rightStaticView.node.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      rightStaticView.node.plan smallQuote
  have smallMappedAbstractSafe : binderSafeAt
      targetDeclaration.quoteConstructor 0
      (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify
          rightStaticView.node.plan.abstractPattern)) = true := by
    have mapped : binderSafeAt
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor) 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify
            rightStaticView.node.plan.abstractPattern)) = true := by
      simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
        smallAbstractSafe
    simpa [targetDeclaration,
      costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] using mapped
  have reconstructedTargetFrame :
      reconstructedNode.reifyTargetFrame smallEnvironment =
        mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify
            rightStaticView.node.plan.abstractPattern) := by
    rw [reconstructedNode.reifyTargetFrame_eq_map_reifiedSourceFrame
      smallEnvironment]
    exact
      reconstructedNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        targetDeclaration.quoteConstructor 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify
            rightStaticView.node.plan.abstractPattern))
        smallMappedAbstractSafe
  obtain ⟨smallQuoteArguments, smallAbstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot
      rightStaticView.node.plan smallQuote
  have smallMappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify
            rightStaticView.node.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (smallQuoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (smallEnvironment.reify argument)) := by
    rw [smallAbstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have smallCanonical_eq_reconstructed : smallCanonical =
      reconstructedNode.canonicalizeReifiedTargetFrame smallEnvironment
        targetDeclaration := by
    unfold smallCanonical
    unfold CostStaticRegionNode.canonicalizeReifiedTargetFrame
    rw [reconstructedTargetFrame, smallMappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have smallRestoreDepth :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        smallEnvironment.restoreAt reconstructedNode.targetBound.length
          smallCanonical := by
    exact smallEnvironment.restoreAt_eq_of_atomTargetSupport_eq_nil
      smallSupportNil smallCanonical restorationDepth
        reconstructedNode.targetBound.length
  have smallRestore_eq_normalize :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (CostStaticRegionNode.normalizeHereditary reconstructedNode
          smallValues).1 := by
    rw [smallRestoreDepth, smallCanonical_eq_reconstructed]
    rfl
  have reconstructedNormalize_eq_tree :
      (CostStaticRegionNode.normalizeHereditary reconstructedNode
        smallValues).1 =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    let reconstructedTree : CostRegionTree rhoCIGSLT targetFree
        rightReached.sourceAvailable [] rightPayload
        (mapTypeExpr (color.symbols rhoCIGSLT)
          rightReached.sourceType) :=
      (((CostRegionTree.static (outer := []) reconstructedNode
          rightStaticView.children).reindexPattern
            rightStaticView.patternEq).reindexAvailable
              rightStaticView.availableEq).reindexType
                rightStaticView.typeEq
    let reconstructedView : reconstructedTree.StaticRootView color :=
      { node := reconstructedNode
        children := rightStaticView.children
        patternEq := rightStaticView.patternEq
        availableEq := rightStaticView.availableEq
        typeEq := rightStaticView.typeEq
        treeEq := rfl }
    have exposedNormal := (reconstructedView.normalize_pattern
      rhoHereditaryStaticNormalizer).symm
    have treeNormal := CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel reconstructedTree rightTree
        rightAdmission.object
    exact exposedNormal.trans treeNormal
  have smallRestore_eq_treeNormal :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    smallRestore_eq_normalize.trans reconstructedNormalize_eq_tree
  have smallCanonicalSafe : binderSafeAt targetDeclaration.quoteConstructor 0
      smallCanonical = true := by
    exact canonicalizeByAt_binderSafeAt
      (CostStaticRegionNode.semanticPatternKeyAt smallEnvironment)
      targetDeclaration targetDeclaration.quoteConstructor 0 0
      (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify
          rightStaticView.node.plan.abstractPattern))
      smallMappedAbstractSafe
  obtain ⟨smallCanonicalTypedRaw, _smallCanonicalSupportSafe⟩ :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_ofInventory_supportSafe
      reconstructedNode smallValues smallInventory
  have smallCanonicalTyped : WellSorted.HasType
      rhoCIGSLT.costWholeLanguage smallEnvironment.atomFreeContext
      reconstructedNode.targetBound smallCanonical
      (.base (color.mapLangSort rhoCIGSLT reconstructedNode.sourceSort).1) := by
    rw [smallCanonical_eq_reconstructed]
    exact smallCanonicalTypedRaw
  have smallSupportFunctionNil : smallEnvironment.restorationSupport =
      fun _ => [] := by
    funext name
    unfold CostStaticAtomEnvironment.restorationSupport
    split
    · rename_i slot selected
      exact smallSupportNil slot
    · rfl
  have smallCanonicalSafeAtNil :
      smallCanonicalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile
        smallEnvironment.restorationSupport [] := by
    rw [smallSupportFunctionNil]
    exact smallCanonicalTyped.reflectiveSupportSafeAt_empty []
  have restoredSmallSafe : binderSafeAt targetDeclaration.quoteConstructor 0
      (smallEnvironment.restoreAt 0 smallCanonical) = true := by
    exact smallCanonicalSafeAtNil.substituteBinderSafeAt
      smallEnvironment.restorationSupportedOpenAssignment targetDeclaration
      (rho_costStaticReflectivePresentationDecl_mem color) (Nat.le_refl 0)
      smallCanonicalSafe
  have smallRestoreZero_eq_treeNormal :
      smallEnvironment.restoreAt 0 smallCanonical =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    exact (smallEnvironment.restoreAt_eq_of_atomTargetSupport_eq_nil
      smallSupportNil smallCanonical 0 restorationDepth).trans
        smallRestore_eq_treeNormal
  have treeNormalScoped :
      (rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)
        ).pattern.isWellScopedAt 0 = true := by
    rw [← smallRestoreZero_eq_treeNormal]
    exact isWellScopedAt_of_binderSafeAt targetDeclaration.quoteConstructor
      restoredSmallSafe
  let largeCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt largeEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (largeEnvironment.reify largePlan.abstractPattern))
  let parentCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt rightEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (rightEnvironment.reify largePlan.abstractPattern))
  have smallToParentRaw :=
    (viewToRestricted restorationDepth).trans
      (largeToParent restorationDepth)
  have parentCanonical_eq_rightFrame : parentCanonical = rightFrame := by
    exact rightTargetCanonicalEq.symm.trans rightFrame_eq.symm
  have rightRestore_eq_treeNormal :
      rightEnvironment.restoreAt restorationDepth rightFrame =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    rw [← parentCanonical_eq_rightFrame]
    exact smallToParentRaw.symm.trans smallRestore_eq_treeNormal
  have endpointEq :
      ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          leftEnvironment.restorationSupport
          leftEnvironment.restorationAssignment restorationDepth
          (.fvar (leftEnvironment.atomName leftSlot)) =
        ReflectiveContextSupport.substituteAt
          rhoCIGSLT.costWholeReflectionProfile
          rightEnvironment.restorationSupport
          rightEnvironment.restorationAssignment restorationDepth
          rightFrame := by
    change leftEnvironment.restoreAt restorationDepth
        (.fvar (leftEnvironment.atomName leftSlot)) =
      rightEnvironment.restoreAt restorationDepth rightFrame
    rw [rightRestore_eq_treeNormal]
    rw [leftEnvironment.restoreAt_atomName_eq_normal_of_scoped leftSlot
      (by rw [leftNormal]; exact treeNormalScoped) restorationDepth]
    exact leftNormal
  exact leftFactor.trans (endpointEq.trans rightFactor.symm)

/-- Every certified-boundary plan stop is source aligned, including the two
authored-Quote orientations.  The non-Quote cells use the finite root
switchboard; the Quote cells share one cospan-parametric sealed-root proof. -/
noncomputable def rhoPlanStopBoundarySide_sourceAligned
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (parentMeasure : Nat)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopBoundarySideCell := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  have nonQuote := rhoPlanStopBoundaryNonQuote_sourceAligned leftView rightView
    declarationColor parentMeasure rightRootAdmissible closeSmaller
  rcases cell with leftBoundaryClass | rightBoundaryClass
  · by_cases rightQuote : rightReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · obtain ⟨leftBoundary⟩ :=
        leftReached.nonempty_boundaryView_of_boundaryClass leftBoundaryClass
      obtain ⟨leftEmbedding'⟩ := leftEmbedding
      obtain ⟨rightEmbedding'⟩ := rightEmbedding
      have aligned :=
        boundaryQuotePlanStops_sourcePatternLeafAligned_withCospan_of_closeSmaller
          leftView.node rightView.node leftView.children rightView.children
          leftEnvironment rightEnvironment cospan leftReached rightReached
          leftBoundary rightAdmission rightQuote sourceTypeEq sourceAvailableEq
          leftEmbedding' rightEmbedding' rightEndpointAdmissible
          rawDeclaration rawAligned (fun stopped => stopped.1.2)
          rightPayloadSizeLe closeSmaller callbackAvailable callbackScope
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact nonQuote callbackAvailable callbackScope leftReached rightReached
        leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute ⟨rightRoute'⟩ stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
        (Or.inl ⟨leftBoundaryClass, rightQuote⟩)
  · by_cases leftQuote : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · obtain ⟨rightBoundary⟩ :=
        rightReached.nonempty_boundaryView_of_boundaryClass rightBoundaryClass
      obtain ⟨leftEmbedding'⟩ := leftEmbedding
      obtain ⟨rightEmbedding'⟩ := rightEmbedding
      have leftEndpointAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
        rw [sourceTypeEq]
        exact rightEndpointAdmissible
      let swappedStop : Pattern → Pattern → Prop := fun right left =>
        RhoCanonicalRawStop declarationColor parentMeasure left right
      have swappedAligned : CanonicalStopAligned rawDeclaration swappedStop
          rightPayload leftPayload :=
        _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStopAligned.flip_mono
          (fun given => given) rawAligned
      have swappedCanonical : ∀ {right left}, swappedStop right left →
          canonicalize rawDeclaration right =
            canonicalize rawDeclaration left := by
        intro rightChild leftChild stopped
        exact stopped.1.2.symm
      have closeSmallerSwapped :
          ∀ {childAvailable childOuter : List TypeExpr}
            {rightChild leftChild : Pattern} {childType : TypeExpr},
            ReflectiveWellSorted.OpenPatternWellSorted
                rhoCIGSLT.costWholeReflectionProfile
                rhoCIGSLT.costWholeLanguage targetFree childAvailable
                childType rightChild →
            ReflectiveWellSorted.OpenPatternWellSorted
                rhoCIGSLT.costWholeReflectionProfile
                rhoCIGSLT.costWholeLanguage targetFree childAvailable
                childType leftChild →
            canonicalize rawDeclaration rightChild =
                canonicalize rawDeclaration leftChild →
            sizeOf rightChild + sizeOf leftChild <
                sizeOf rightView.node.term.1 + sizeOf leftView.node.term.1 →
            rhoCanonicalRecursiveTypeDomain.Admissible childType →
            Nonempty (CostCanonicalPairElaboration rhoCIGSLT
              rhoHereditaryNormalizationKernel targetFree childAvailable
              childOuter rightChild leftChild childType) := by
        intro childAvailable childOuter rightChild leftChild childType
          rightWellSorted leftWellSorted canonical smaller admissible
        obtain ⟨pair⟩ := closeSmaller leftWellSorted rightWellSorted
          canonical.symm (by omega) admissible
        exact ⟨pair.symm⟩
      have swapped :=
        boundaryQuotePlanStops_sourcePatternLeafAligned_withCospan_of_closeSmaller
          rightView.node leftView.node rightView.children leftView.children
          rightEnvironment leftEnvironment cospan.symm rightReached leftReached
          rightBoundary leftAdmission leftQuote sourceTypeEq.symm
          sourceAvailableEq.symm rightEmbedding' leftEmbedding'
          leftEndpointAdmissible rawDeclaration swappedAligned
          swappedCanonical leftPayloadSizeLe closeSmallerSwapped
          callbackAvailable callbackScope
      have aligned := PatternLeafAligned.flip_mono
        (transposed := fun leftLeaf rightLeaf => ∀ sourceDepth,
          ReflectiveContextSupport.RestoresTogether
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment
              (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
                (leftView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
              (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
                (rightView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
        (fun related sourceDepth => by
          simpa only [CostStaticAtomKeyCospan.symm_commonSupport,
            CostStaticAtomKeyCospan.symm_commonAssignment,
            CostStaticAtomKeyCospan.symm_reifyWith,
            CostStaticAtomKeyCospan.symm_leftSlot,
            CostStaticAtomKeyCospan.symm_rightSlot] using
            (related sourceDepth).symm) swapped
      simpa only [← leftAbstractEq, ← rightAbstractEq] using aligned
    · exact nonQuote callbackAvailable callbackScope leftReached rightReached
        leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute ⟨rightRoute'⟩ stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
        (Or.inr ⟨leftQuote, rightBoundaryClass⟩)

/-- A strictly smaller pair of reached authored Quotes has an exact apex in
the enclosing semantic-atom cospan. -/
noncomputable def quotePlanStops_commonRestorationApex_of_closeSmaller
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (rightRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
        rightPayload)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute
      rightRootAdmissible
  have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree leftReached.sourceAvailable
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
      rightPayload := by
    rw [sourceAvailableEq, sourceTypeEq]
    exact rightAdmission.wellSorted
  have canonical := rawAligned.canonicalize_eq
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    (fun stopped => stopped.1.2)
  let pair := Classical.choice
    (closeSmaller (childOuter := []) leftAdmission.wellSorted rightWellSorted
      canonical smaller leftAdmissible)
  let rightTree : CostRegionTree rhoCIGSLT targetFree
      rightReached.sourceAvailable [] rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostRegionTree.reindexFiber sourceAvailableEq rfl
      (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq)
        pair.rightTree
  have pairNormal :
      (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have alignmentNormal :
        (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      simpa only [rhoHereditaryNormalizationKernel] using
        pair.alignment.normalize_pattern_eq
    exact alignmentNormal.trans (by simp [rightTree])
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftFrame := leftView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
          leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern)))
  let rightFrame := rightView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
          rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)))
  have leftCovered : leftEnvironment.Covers leftFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        leftView.node leftEnvironment leftReached callbackAvailable
          callbackScope
  have rightCovered : rightEnvironment.Covers rightFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        rightView.node rightEnvironment rightReached callbackAvailable
          callbackScope
  have leftRestore : ∀ restorationDepth,
      leftEnvironment.restoreAt restorationDepth leftFrame =
        (pair.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        leftView.node leftView.children leftEnvironment leftReached
          leftAdmission leftQuote leftEmbedding pair.leftTree callbackAvailable
            callbackScope restorationDepth
  have rightRestore : ∀ restorationDepth,
      rightEnvironment.restoreAt restorationDepth rightFrame =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        rightView.node rightView.children rightEnvironment rightReached
          rightAdmission rightQuote rightEmbedding rightTree callbackAvailable
            callbackScope restorationDepth
  subst leftAbstractEq
  subst rightAbstractEq
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro restorationDepth
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
      restorationDepth leftFrame leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
      restorationDepth rightFrame rightCovered
  have endpointEq : leftEnvironment.restoreAt restorationDepth leftFrame =
      rightEnvironment.restoreAt restorationDepth rightFrame :=
    (leftRestore restorationDepth).trans
      (pairNormal.trans (rightRestore restorationDepth).symm)
  exact leftFactor.trans (endpointEq.trans rightFactor.symm)

/-- A certified-boundary stop reached inside an already reached pair retains
its parent-cospan apex after composing contexts, entry embeddings, and type
routes back to the static roots. -/
noncomputable def nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (parentMeasure : Nat)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries)
    (rightParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries)
    (leftParentRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType))
    (rightParentRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftParentReached.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightParentReached.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
        leftParentReached.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
        rightParentReached.plan.boundaryTable.entries)
    (leftRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) leftParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType))
    (rightRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) rightParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (stopReason : RhoCanonicalRawStop declarationColor parentMeasure
        leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftParentPayload)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightParentPayload)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
        rightPayload)
    (notBothBoundary : ¬
      (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary))
    (cell : RhoPlanStopBoundarySideCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let leftReached' := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightReached' := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  have sourceAligned := rhoPlanStopBoundarySide_sourceAligned leftView
    rightView declarationColor parentMeasure rightRootAdmissible closeSmaller
  have aligned := sourceAligned callbackAvailable callbackScope leftReached'
    rightReached' leftAdmission rightAdmission leftAbstractEq rightAbstractEq
    sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    ⟨leftEmbedding.comp leftParentEmbedding⟩
    ⟨rightEmbedding.comp rightParentEmbedding⟩
    ⟨leftParentRoute.prepend leftRoute⟩
    ⟨rightParentRoute.prepend rightRoute⟩ stopReason
    (leftPayloadSizeLe.trans leftParentSizeLe)
    (rightPayloadSizeLe.trans rightParentSizeLe) rawAligned notBothBoundary
    cell
  exact RhoStaticPlanStopCommonApex.ofSourcePatternLeafAligned leftView.node
    rightView.node (leftView.targetBound_eq_targetBound rightView) _ _ aligned
    callbackScope callbackRoot

/-- A nested pair of certified-boundary stops retains its exact apex after
both reached contexts, entry embeddings, and the target-fibre route are
composed back to the enclosing static roots. -/
noncomputable def nestedBoundaryPairPlanStops_commonRestorationApex_of_closeSmaller
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries)
    (rightParentEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries)
    (rightParentRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType))
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftParentReached.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightParentReached.plan.abstractPattern)
    (_leftAdmission : leftReached.plan.RawAdmission)
    (_rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
        leftParentReached.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
        rightParentReached.plan.boundaryTable.entries)
    (rightRoute : CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
        rightPayload)
    (leftBoundaryClass : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightBoundaryClass : rightReached.plan.rootClass.IsCertifiedBoundary) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let leftReached' := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightReached' := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  obtain ⟨leftBoundary⟩ :=
    leftReached'.nonempty_boundaryView_of_boundaryClass leftBoundaryClass
  obtain ⟨rightBoundary⟩ :=
    rightReached'.nonempty_boundaryView_of_boundaryClass rightBoundaryClass
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  have sourceAligned :=
    RhoStaticPlanBoundaryRestoration.boundaryViews_sourcePatternLeafAligned_of_closeSmaller
      leftView.node rightView.node leftView.children rightView.children
      leftEnvironment rightEnvironment leftReached' rightReached'
      leftBoundary rightBoundary sourceTypeEq sourceAvailableEq
      (leftEmbedding.comp leftParentEmbedding)
      (rightEmbedding.comp rightParentEmbedding)
      ⟨rightParentRoute.prepend rightRoute⟩ rightRootAdmissible
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawAligned (fun stopped => stopped.1.2) closeSmaller
      (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
        leftEnvironment)
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
        rightEnvironment)
      callbackAvailable callbackScope
  subst leftAbstractEq
  subst rightAbstractEq
  exact RhoStaticPlanStopCommonApex.ofSourcePatternLeafAligned leftView.node
    rightView.node (leftView.targetBound_eq_targetBound rightView) _ _
    sourceAligned callbackScope callbackRoot

/-- A foreign canonical stop reached below an enclosing stopped pair reduces
to the paired authored-Quote and bare-parallel terminals.  Certified-boundary
stops are discharged here, with both levels of entry embeddings and type
routes composed into the static root cospan. -/
noncomputable def nestedForeignPlanStop_commonRestorationApex_of_quoteParallel
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (foreign : declarationColor ≠ color)
    (stopMeasure : Nat)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType)))
    (rightParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat)
    (quotePair : ∀ {leftPayload rightPayload leftAbstract rightAbstract},
      CostStaticPlanCanonicalStopAtPayload leftParentReached.plan
          rightParentReached.plan rhoReflectivePresentation
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (RhoCanonicalRawStop declarationColor
            stopMeasure)
          leftPayload rightPayload leftAbstract rightAbstract →
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftParentReached.plan.abstractPattern) →
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightParentReached.plan.abstractPattern) →
      leftReached.plan.rootClass =
          .application rhoReflectivePresentation.quoteConstructor →
      rightReached.plan.rootClass =
          .application rhoReflectivePresentation.quoteConstructor →
      RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
        callbackScope callbackRoot leftAbstract rightAbstract)
    (parallelSide : ∀
      {leftPayload rightPayload leftAbstract rightAbstract},
      CostStaticPlanCanonicalStopAtPayload leftParentReached.plan
          rightParentReached.plan rhoReflectivePresentation
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (RhoCanonicalRawStop declarationColor
            stopMeasure)
          leftPayload rightPayload leftAbstract rightAbstract →
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftParentReached.plan.abstractPattern) →
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightParentReached.plan.abstractPattern) →
      (leftReached.plan.rootClass =
          .collection rhoReflectivePresentation.parallelCollection ∨
        rightReached.plan.rootClass =
          .collection rhoReflectivePresentation.parallelCollection) →
      RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
        callbackScope callbackRoot leftAbstract rightAbstract)
    {leftAbstract rightAbstract : Pattern}
    (stopped : CostStaticPlanCanonicalStop leftParentReached.plan
      rightParentReached.plan rhoReflectivePresentation
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor
        stopMeasure)
      leftAbstract rightAbstract) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  rcases stopped with ⟨leftPayload, rightPayload, evidence⟩
  have evidenceForTerminal := evidence
  rcases evidence with
    ⟨leftReached, rightReached, leftAdmission, rightAdmission, leftAbstractEq,
      rightAbstractEq, sourceTypeEq, sourceAvailableEq, sourceBoundEq,
      targetBoundEq, thinningEq, leftEmbedding, rightEmbedding, leftRoute,
      rightRoute, stopReason, leftPayloadSizeLe, rightPayloadSizeLe,
      rawAligned⟩
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨leftParentRoute⟩ := leftParentRoute
  obtain ⟨rightParentRoute⟩ := rightParentRoute
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  obtain ⟨leftRoute⟩ := leftRoute
  obtain ⟨rightRoute⟩ := rightRoute
  by_cases bothBoundary : leftReached.plan.rootClass.IsCertifiedBoundary ∧
      rightReached.plan.rootClass.IsCertifiedBoundary
  · exact nestedBoundaryPairPlanStops_commonRestorationApex_of_closeSmaller
      leftView rightView declarationColor rightRootAdmissible closeSmaller
      leftParentReached rightParentReached leftParentEmbedding
      rightParentEmbedding rightParentRoute callbackAvailable callbackScope
      callbackRoot leftReached rightReached leftAdmission rightAdmission
      leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
      leftEmbedding rightEmbedding rightRoute rawAligned bothBoundary.1
      bothBoundary.2
  · rcases RhoCanonicalRawStop.foreign_reached_stop_cases leftReached
        rightReached foreign stopReason bothBoundary with quote | leftBoundary |
          rightBoundary | leftParallel | rightParallel
    · exact quotePair evidenceForTerminal leftReached rightReached quote.1
        quote.2
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor stopMeasure
        rightRootAdmissible closeSmaller leftParentReached rightParentReached
        leftParentEmbedding rightParentEmbedding leftParentRoute
        rightParentRoute leftParentSizeLe rightParentSizeLe callbackAvailable
        callbackScope callbackRoot leftReached rightReached leftAdmission
        rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
        sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
        rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
        rightPayloadSizeLe rawAligned bothBoundary (Or.inl leftBoundary)
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor stopMeasure
        rightRootAdmissible closeSmaller leftParentReached rightParentReached
        leftParentEmbedding rightParentEmbedding leftParentRoute
        rightParentRoute leftParentSizeLe rightParentSizeLe callbackAvailable
        callbackScope callbackRoot leftReached rightReached leftAdmission
        rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
        sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
        rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
        rightPayloadSizeLe rawAligned bothBoundary (Or.inr rightBoundary)
    · exact parallelSide evidenceForTerminal leftReached rightReached
        (Or.inl leftParallel)
    · exact parallelSide evidenceForTerminal leftReached rightReached
        (Or.inr rightParallel)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
