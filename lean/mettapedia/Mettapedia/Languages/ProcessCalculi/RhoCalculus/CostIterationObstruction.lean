import Mettapedia.GSLT.LanguageDef.CostEndofunctor
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws

/-!
# The compact Cost iteration obstruction for rho

The first Cost layer keeps the base and wrapped process sorts distinct, so a
sort-indexed open section can normalize their shared empty-parallel syntax to
different units.  At the next layer, the old base process sort is no longer
the interacting sort.  Its base and wrapped images therefore coincide, while
the corresponding constructor labels remain distinct.

This file records that obstruction on the proof-relevant region carrier.  It
does not assume a second-layer canonical law: an arbitrary candidate
first-layer law package is enough to construct the two competing elaborations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The generated continued object, parameterized by any honest witness that
rho belongs to the first strict Cost domain. -/
abbrev rhoCostOne (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) : CIGSLT :=
  rhoCIGSLT.costCIGSLT laws

private theorem rhoParallelRule_mem :
    rhoCalc.terms[3] ∈
      rhoCIGSLT.theory.presentation.presentation.language.terms := by
  change rhoCalc.terms[3] ∈ rhoCalc.terms
  simp [rhoCalc]

/-- The first-layer proof-relevant base choice used to compute the unit
selected by rho's own canonical section. -/
private def rhoParallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

private theorem rhoParallelChoice_mem :
    rhoParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base rhoProc.1)) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, rhoParallelRule_mem,
    ?_, rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ rhoParallelRule_mem
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

private def rhoBaseEmptyPlan :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base [])
      [] (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole (.collection .hashBag [] none) (.base rhoProc.1) :=
  .collection rhoParallelChoice rhoParallelChoice_mem .nil

/-- The empty parallel in the first generated base-process fiber. -/
private def rhoBaseEmpty :
    OpenTerm rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) := by
  refine ⟨.collection .hashBag [] none, ?_, rfl, rfl, ?_⟩
  · apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
    · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
        rhoParallelRule_mem
    · exact rho_costBaseParallelConstructor_params
    · exact .nil [] _
  · intro presentation membership
    rfl

private def rhoBaseEmptyNode :
    CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan rhoBaseEmpty rhoBaseEmptyPlan rfl

private def rhoBaseEmptyTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc).1) :=
  .static rhoBaseEmptyNode .nil

private def rhoBaseEmptyElaboration :
    CostOpenElaboration rhoCIGSLT rhoBaseEmpty :=
  ⟨rhoBaseEmptyTree⟩

private theorem rhoBaseEmptyNode_normalizedThickenedSkeletonRaw :
    rhoBaseEmptyNode.normalizedThickenedSkeletonRaw =
      .apply (costBaseConstructorName "PZero") [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      rhoBaseEmptyNode.thinning rfl]
  unfold normalizeCostStaticStratum
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        rhoBaseEmptyNode.skeleton.1) =
    _
  rw [rhoBaseEmptyNode.skeleton_pattern]
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (.collection .hashBag [] none)) =
    _
  rw [
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_parallel_empty]
  rfl

private theorem rhoBaseEmpty_normalized_pattern :
    rhoBaseEmptyElaboration.normalizeErasure.1 =
      .apply (costBaseConstructorName "PZero") [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  change rhoBaseEmptyTree.normalize.pattern = _
  unfold rhoBaseEmptyTree
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      rhoBaseEmptyNode .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoBaseEmptyNode_normalizedThickenedSkeletonRaw]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

private theorem rhoCostNormalizeOpen_baseEmpty :
    (rhoCIGSLT.costNormalizeOpen rhoBaseEmpty).1 =
      .apply (costBaseConstructorName "PZero") [] := by
  calc
    (rhoCIGSLT.costNormalizeOpen rhoBaseEmpty).1 =
        (CostOpenElaboration.compile rhoCIGSLT rhoBaseEmpty
          ).normalizeErasure.1 := rfl
    _ = rhoBaseEmptyElaboration.normalizeErasure.1 :=
      congrArg (fun term => term.1)
        (CostCanonicalLaws.rho_compactCostNormalizationCoherent rhoBaseEmpty
          (CostOpenElaboration.compile rhoCIGSLT rhoBaseEmpty)
          rhoBaseEmptyElaboration)
    _ = _ := rhoBaseEmpty_normalized_pattern

/-- The base image of rho parallel composition, viewed as an authored rule of
the first generated Cost object. -/
private def baseParallelRule : GrammarRule :=
  costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3]

private theorem baseParallelRule_mem
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    baseParallelRule ∈
      (rhoCostOne laws).theory.presentation.presentation.language.terms :=
  rhoCIGSLT.costBaseConstructor_mem_costWhole rhoCalc.terms[3]
    rhoParallelRule_mem

private theorem baseParallelRule_wrapped
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    baseParallelRule.label ∈
      (rhoCostOne laws).continuationRetyping.wrappedLabels := by
  apply (rhoCostOne laws).bareCollectionConstructorsWrapped baseParallelRule
  · exact baseParallelRule_mem laws
  · change ∃ parameterName collectionType elementType,
      baseParallelRule.params =
        [.simple parameterName (.collection collectionType elementType)]
    exact ⟨"ps", .hashBag, .base (costBaseSortName "Proc"),
      rho_costBaseParallelConstructor_params⟩

private theorem baseParallelRule_noninteracting
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    baseParallelRule.category ≠
      (rhoCostOne laws).theory.presentation.interactingSort.1.name :=
  costBaseSortName_ne_wrapped "Proc"

private theorem baseParallelRule_params :
    baseParallelRule.params =
      [.simple "ps"
        (.collection .hashBag (.base (costBaseSortName "Proc")))] :=
  rho_costBaseParallelConstructor_params

private def sourceSort (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    LangSort (rhoCostOne laws).theory.presentation.presentation.language :=
  ⟨baseParallelRule.category,
    Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.termCategory_mem_of_validate_eq_nil
      _ (rhoCostOne laws).theory.presentation.presentation.valid _
        (baseParallelRule_mem laws)⟩

private def parallelChoice : CostCollectionTypingChoice :=
  .bare baseParallelRule (.base (costBaseSortName "Proc"))

/-- The same declaration-derived empty parallel choice occurs in both
second-layer static colours. -/
theorem emptyParallelChoice_crossColor
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    let source := rhoCostOne laws
    let expected :=
      mapTypeExpr (CostStaticColor.base.symbols source)
        (.base baseParallelRule.category)
    parallelChoice ∈
        costStaticCollectionTypingChoices source .base
          FreeTypeContext.empty [] .hashBag [] expected ∧
      parallelChoice ∈
        costStaticCollectionTypingChoices source .wrapped
          FreeTypeContext.empty [] .hashBag [] expected := by
  exact crossColorEmptyBareCollectionCandidate
    (rhoCostOne laws) FreeTypeContext.empty [] .hashBag baseParallelRule
      (.base (costBaseSortName "Proc")) (baseParallelRule_mem laws)
      (baseParallelRule_wrapped laws)
      (baseParallelRule_noninteracting laws) "ps" baseParallelRule_params

private theorem baseChoice_mem
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    parallelChoice ∈
      costStaticCollectionTypingChoices (rhoCostOne laws) .base
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols (rhoCostOne laws))
          (.base (sourceSort laws).1)) :=
  (emptyParallelChoice_crossColor laws).1

private theorem wrappedChoice_mem
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    parallelChoice ∈
      costStaticCollectionTypingChoices (rhoCostOne laws) .wrapped
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.wrapped.symbols (rhoCostOne laws))
          (.base (sourceSort laws).1)) := by
  have overlap :=
    (CostStaticColor.mapTypeExpr_base_eq_wrapped_iff
      (rhoCostOne laws) (.base (sourceSort laws).1)).2 (by
        simpa [sourceSort, TypeExpr.baseNames] using
          (fun equality =>
            baseParallelRule_noninteracting laws equality.symm))
  rw [← overlap]
  exact (emptyParallelChoice_crossColor laws).2

private def basePlan (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostStaticRegionPlan (rhoCostOne laws) .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget
        (rhoCostOne laws) .base [])
      [] (CostStaticBinderThinning.ofTargetThinning
        (rhoCostOne laws) .base [])
      [] .hole (.collection .hashBag [] none)
      (.base (sourceSort laws).1) :=
  .collection parallelChoice (baseChoice_mem laws) .nil

private def wrappedPlan (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostStaticRegionPlan (rhoCostOne laws) .wrapped FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget
        (rhoCostOne laws) .wrapped [])
      [] (CostStaticBinderThinning.ofTargetThinning
        (rhoCostOne laws) .wrapped [])
      [] .hole (.collection .hashBag [] none)
      (.base (sourceSort laws).1) :=
  .collection parallelChoice (wrappedChoice_mem laws) .nil

private theorem nextBaseParallelRule_params
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (costBaseConstructor (rhoCostOne laws).cut baseParallelRule).params =
      [.simple "ps"
        (.collection .hashBag
          (mapTypeExpr (CostStaticColor.base.symbols (rhoCostOne laws))
            (.base (costBaseSortName "Proc"))))] := by
  rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabels
    (rhoCostOne laws) baseParallelRule (baseParallelRule_mem laws)
      (baseParallelRule_wrapped laws), baseParallelRule_params]
  rfl

private theorem emptyParallel_typed
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    HasType (rhoCostOne laws).costWholeLanguage FreeTypeContext.empty []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (rhoCostOne laws) (sourceSort laws)).1) := by
  have typed :
      HasType (rhoCostOne laws).costWholeLanguage FreeTypeContext.empty []
        (.collection .hashBag [] none)
        (.base
          (costBaseConstructor
            (rhoCostOne laws).cut baseParallelRule).category) := by
    apply HasType.collectionConstructor
        (rule := costBaseConstructor (rhoCostOne laws).cut baseParallelRule)
        (parameterName := "ps")
        (elementType :=
          mapTypeExpr (CostStaticColor.base.symbols (rhoCostOne laws))
            (.base (costBaseSortName "Proc")))
    · exact (rhoCostOne laws).costBaseConstructor_mem_costWhole
        baseParallelRule (baseParallelRule_mem laws)
    · exact nextBaseParallelRule_params laws
    · exact .nil [] _
  simpa [sourceSort, CostStaticColor.symbols, costBaseStaticSymbols,
    costBasePresentationSymbols, costBaseConstructor] using typed

private def emptyParallel
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    OpenTerm (rhoCostOne laws).costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort
        (rhoCostOne laws) (sourceSort laws)) := by
  refine ⟨.collection .hashBag [] none, emptyParallel_typed laws,
    rfl, rfl, ?_⟩
  intro declaration membership
  rfl

private theorem colorOverlap
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostStaticColor.base.mapLangSort (rhoCostOne laws) (sourceSort laws) =
      CostStaticColor.wrapped.mapLangSort
        (rhoCostOne laws) (sourceSort laws) :=
  (CostStaticColor.mapLangSort_base_eq_wrapped_iff
    (rhoCostOne laws) (sourceSort laws)).2
      (baseParallelRule_noninteracting laws)

private def wrappedEmptyParallel
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    OpenTerm (rhoCostOne laws).costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.wrapped.mapLangSort
        (rhoCostOne laws) (sourceSort laws)) :=
  OpenTerm.reindex rfl rfl (colorOverlap laws) (emptyParallel laws)

private def baseNode
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostStaticRegionNode (rhoCostOne laws) .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan (emptyParallel laws) (basePlan laws) rfl

private def wrappedNode
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostStaticRegionNode (rhoCostOne laws) .wrapped FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan
    (wrappedEmptyParallel laws) (wrappedPlan laws) rfl

private theorem baseNode_sourceSort
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (baseNode laws).sourceSort =
      CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc := by
  apply Subtype.ext
  rfl

private theorem baseNode_sourceBound
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (baseNode laws).sourceBound = [] := by
  change
    CostStaticBinderThinning.sourceContextOfTarget (rhoCostOne laws) .base
      (baseNode laws).targetBound = []
  rw [show (baseNode laws).targetBound = [] by rfl]
  simp [CostStaticBinderThinning.sourceContextOfTarget]

private theorem wrappedNode_sourceSort
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (wrappedNode laws).sourceSort =
      CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc := by
  apply Subtype.ext
  rfl

private theorem wrappedNode_sourceBound
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (wrappedNode laws).sourceBound = [] := by
  change
    CostStaticBinderThinning.sourceContextOfTarget (rhoCostOne laws) .wrapped
      (wrappedNode laws).targetBound = []
  rw [show (wrappedNode laws).targetBound = [] by rfl]
  simp [CostStaticBinderThinning.sourceContextOfTarget]

private theorem baseNode_skeleton_pattern_eq
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (.collection .hashBag [] none : Pattern) =
      (baseNode laws).skeleton.1 := by
  rfl

private theorem wrappedNode_skeleton_pattern_eq
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (.collection .hashBag [] none : Pattern) =
      (wrappedNode laws).skeleton.1 := by
  rfl

private theorem rhoParallelChoice_memAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty) :
    rhoParallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base
        node.boundaryTable.sourceFreeContext
        node.sourceBound .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base rhoProc.1)) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, rhoParallelRule_mem,
    ?_, rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ rhoParallelRule_mem
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

private def rhoBaseEmptyPlanAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty) :
    CostStaticRegionPlan rhoCIGSLT .base
      node.boundaryTable.sourceFreeContext
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        node.sourceBound)
      node.sourceBound
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base
        node.sourceBound)
      node.sourceBound .hole
      (.collection .hashBag [] none) (.base rhoProc.1) :=
  .collection rhoParallelChoice (rhoParallelChoice_memAt laws node) .nil

private def rhoBaseEmptyAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty) :
    OpenTerm rhoCIGSLT.costWholeLanguage
      node.boundaryTable.sourceFreeContext
      node.sourceBound
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) := by
  refine ⟨.collection .hashBag [] none, ?_, rfl, rfl, ?_⟩
  · apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
    · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
        rhoParallelRule_mem
    · exact rho_costBaseParallelConstructor_params
    · exact .nil _ _
  · intro presentation membership
    rfl

private def rhoBaseEmptyNodeAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty) :
    CostStaticRegionNode rhoCIGSLT .base
      node.boundaryTable.sourceFreeContext :=
  CostStaticRegionNode.ofPlan (rhoBaseEmptyAt laws node)
    (rhoBaseEmptyPlanAt laws node) rfl

private def rhoBaseEmptyTreeAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty) :
    CostRegionTree rhoCIGSLT
      node.boundaryTable.sourceFreeContext
      node.sourceBound []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc).1) :=
  .static (rhoBaseEmptyNodeAt laws node) .nil

private theorem sourceNode_sourceType_eq
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) :
    (.base (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc).1 :
      TypeExpr) =
      .base node.sourceSort.1 :=
  congrArg (fun sort : LangSort rhoCIGSLT.costWholeLanguage =>
    (.base sort.1 : TypeExpr)) sourceSortEq.symm

private def rhoBaseEmptyElaborationAt
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    CostOpenElaboration rhoCIGSLT node.skeleton :=
  ⟨((rhoBaseEmptyTreeAt laws node).reindexType
      (sourceNode_sourceType_eq laws node sourceSortEq)).reindexPattern
        patternEq⟩

private theorem rhoBaseEmptyElaborationAt_normalize_eq
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    (rhoBaseEmptyElaborationAt laws node sourceSortEq
      patternEq).tree.normalize.pattern =
      (rhoBaseEmptyTreeAt laws node).normalize.pattern := by
  exact (CostRegionTree.reindexPattern_normalize
    (patternEq := patternEq)
    (tree := (rhoBaseEmptyTreeAt laws node).reindexType
      (sourceNode_sourceType_eq laws node sourceSortEq))).trans
        (CostRegionTree.reindexType_normalize
          (typeEq := sourceNode_sourceType_eq laws node sourceSortEq)
          (tree := rhoBaseEmptyTreeAt laws node))

private theorem rhoBaseEmptyNodeAt_normalizedThickenedSkeletonRaw
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty)
    (sourceBoundEq : node.sourceBound = []) :
    (rhoBaseEmptyNodeAt laws node).normalizedThickenedSkeletonRaw =
      .apply (costBaseConstructorName "PZero") [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (rhoBaseEmptyNodeAt laws node).thinning sourceBoundEq]
  unfold normalizeCostStaticStratum
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (rhoBaseEmptyNodeAt laws node).skeleton.1) =
    _
  rw [(rhoBaseEmptyNodeAt laws node).skeleton_pattern]
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (.collection .hashBag [] none)) =
    _
  rw [
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_parallel_empty]
  rfl

private theorem rhoBaseEmptyElaborationAt_normalized_pattern
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT)
    (node : CostStaticRegionNode (rhoCostOne laws) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (sourceBoundEq : node.sourceBound = [])
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    (rhoBaseEmptyElaborationAt laws node sourceSortEq
      patternEq).normalizeErasure.1 =
      .apply (costBaseConstructorName "PZero") [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  rw [rhoBaseEmptyElaborationAt_normalize_eq laws node sourceSortEq patternEq]
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (rhoBaseEmptyNodeAt laws node) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoBaseEmptyNodeAt_normalizedThickenedSkeletonRaw laws node sourceBoundEq]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

private theorem sourceNode_sourceCanonical
    {color : CostStaticColor}
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ∀ (node : CostStaticRegionNode (rhoCostOne laws) color
        FreeTypeContext.empty)
      (_sourceSortEq :
        node.sourceSort =
          CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
      (_sourceBoundEq : node.sourceBound = [])
      (_patternEq : (.collection .hashBag [] none : Pattern) =
        node.skeleton.1),
      ((rhoCostOne laws).openCanonical.normalize node.skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] := by
  intro node _sourceSortEq _sourceBoundEq _patternEq
  change (rhoCIGSLT.costNormalizeOpen node.skeleton).1 = _
  calc
    (rhoCIGSLT.costNormalizeOpen node.skeleton).1 =
        (CostOpenElaboration.compile rhoCIGSLT
          node.skeleton).normalizeErasure.1 := rfl
    _ = (rhoBaseEmptyElaborationAt laws node _sourceSortEq
          _patternEq).normalizeErasure.1 :=
      congrArg (fun term => term.1)
        (CostCanonicalLaws.rho_compactCostNormalizationCoherent node.skeleton
          (CostOpenElaboration.compile rhoCIGSLT
            node.skeleton)
          (rhoBaseEmptyElaborationAt laws node _sourceSortEq _patternEq))
    _ = _ := rhoBaseEmptyElaborationAt_normalized_pattern laws node
      _sourceSortEq _sourceBoundEq _patternEq

private theorem baseNode_sourceCanonical
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ((rhoCostOne laws).openCanonical.normalize
      (baseNode laws).skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] :=
  sourceNode_sourceCanonical laws (baseNode laws)
    (baseNode_sourceSort laws) (baseNode_sourceBound laws)
      (baseNode_skeleton_pattern_eq laws)

private theorem wrappedNode_sourceCanonical
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ((rhoCostOne laws).openCanonical.normalize
      (wrappedNode laws).skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] :=
  sourceNode_sourceCanonical laws (wrappedNode laws)
    (wrappedNode_sourceSort laws) (wrappedNode_sourceBound laws)
      (wrappedNode_skeleton_pattern_eq laws)

private theorem baseNode_normalizedThickenedSkeletonRaw
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (baseNode laws).normalizedThickenedSkeletonRaw =
      .apply
        (costBaseConstructorName (costBaseConstructorName "PZero")) [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (baseNode laws).thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [baseNode_sourceCanonical laws]
  rfl

private theorem wrappedNode_normalizedThickenedSkeletonRaw
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (wrappedNode laws).normalizedThickenedSkeletonRaw =
      .apply
        (costWrappedConstructorName (costBaseConstructorName "PZero")) [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (wrappedNode laws).thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [wrappedNode_sourceCanonical laws]
  rfl

private def baseTree
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostRegionTree (rhoCostOne laws) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (rhoCostOne laws) (sourceSort laws)).1) :=
  .static (baseNode laws) .nil

private def wrappedTreeNatural
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostRegionTree (rhoCostOne laws) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.wrapped.mapLangSort
        (rhoCostOne laws) (sourceSort laws)).1) :=
  .static (wrappedNode laws) .nil

private theorem colorOverlapType
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (.base (CostStaticColor.wrapped.mapLangSort
      (rhoCostOne laws) (sourceSort laws)).1 : TypeExpr) =
    .base (CostStaticColor.base.mapLangSort
      (rhoCostOne laws) (sourceSort laws)).1 :=
  congrArg (fun sort : LangSort (rhoCostOne laws).costWholeLanguage =>
    (.base sort.1 : TypeExpr)) (colorOverlap laws).symm

private def wrappedTree
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostRegionTree (rhoCostOne laws) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (rhoCostOne laws) (sourceSort laws)).1) := by
  exact (wrappedTreeNatural laws).reindexType (colorOverlapType laws)

private theorem wrappedTree_normalize_eq
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (wrappedTree laws).normalize.pattern =
      (wrappedTreeNatural laws).normalize.pattern :=
  CostRegionTree.reindexType_normalize
    (typeEq := colorOverlapType laws) (tree := wrappedTreeNatural laws)

private def baseElaboration
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostOpenElaboration (rhoCostOne laws) (emptyParallel laws) :=
  ⟨baseTree laws⟩

private def wrappedElaboration
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    CostOpenElaboration (rhoCostOne laws) (emptyParallel laws) :=
  ⟨wrappedTree laws⟩

private theorem base_normalized_pattern
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (baseElaboration laws).normalizeErasure.1 =
      .apply
        (costBaseConstructorName (costBaseConstructorName "PZero")) [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  change (baseTree laws).normalize.pattern = _
  unfold baseTree
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (baseNode laws) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    baseNode_normalizedThickenedSkeletonRaw laws]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

private theorem wrapped_normalized_pattern
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    (wrappedElaboration laws).normalizeErasure.1 =
      .apply
        (costWrappedConstructorName (costBaseConstructorName "PZero")) [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  change (wrappedTree laws).normalize.pattern = _
  rw [wrappedTree_normalize_eq laws]
  unfold wrappedTreeNatural
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (wrappedNode laws) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    wrappedNode_normalizedThickenedSkeletonRaw laws]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

/-- Exact compact coherence is not closed by a second Cost application on
rho.  The same checked compact empty parallel has base- and wrapped-colour
elaborations whose normalized units retain distinct constructor identities. -/
theorem rhoCostOne_not_compactCostNormalizationCoherent
    (laws : CIGSLT.CostOneObjectLaws rhoCIGSLT) :
    ¬ CompactCostNormalizationCoherent (rhoCostOne laws) := by
  intro coherent
  have equal :=
    congrArg (fun term => term.1)
      (coherent (emptyParallel laws)
        (baseElaboration laws) (wrappedElaboration laws))
  rw [base_normalized_pattern, wrapped_normalized_pattern] at equal
  have labelsEqual :
      costBaseConstructorName (costBaseConstructorName "PZero") =
        costWrappedConstructorName (costBaseConstructorName "PZero") := by
    injection equal
  exact costBaseConstructorName_ne_wrapped
    (costBaseConstructorName "PZero")
    (costBaseConstructorName "PZero") labelsEqual

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction
