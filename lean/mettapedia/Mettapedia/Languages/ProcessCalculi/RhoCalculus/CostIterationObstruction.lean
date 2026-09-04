import Mettapedia.GSLT.LanguageDef.Cost.Construction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical

/-!
# The compact Cost iteration obstruction for rho

The first Cost layer keeps the base and wrapped process sorts distinct, so a
sort-indexed open section can normalize their shared empty-parallel syntax to
different units.  At the next layer, the old base process sort is no longer
the interacting sort.  Its base and wrapped images therefore coincide, while
the corresponding constructor labels remain distinct.

This file records that obstruction on the proof-relevant region carrier.  It
does not assume a second-layer canonical law.  The first-layer normalizer is
arbitrary except for one explicit representative fact: empty parallel remains
rho's base unit in every boundary context used by the witness.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The generated continued object selected by the original reference
normalizer.  Rho refutes this law bundle; the definition is retained only to
state that negative compatibility boundary explicitly. -/
abbrev rhoReferenceCostLayer
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) : CIGSLT :=
  rhoCIGSLT.costCIGSLTReference laws

/-- A choice of first-layer rho Cost normalizer together with its exact object
laws.  The generated syntax is fixed by `rhoCIGSLT`; only the canonical open
section varies. -/
structure RhoCostLayerConfiguration where
  normalizeOpen : CostOpenNormalizer rhoCIGSLT
  laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT normalizeOpen

namespace RhoCostLayerConfiguration

/-- The first generated Cost object selected by a normalizer configuration. -/
def source (configuration : RhoCostLayerConfiguration) : CIGSLT :=
  rhoCIGSLT.costCIGSLTWith configuration.normalizeOpen configuration.laws

/-- The original reference executor as one point in the parameterized family.
Rho has no inhabitant of this input type; use `hereditary` for the repaired
construction. -/
def reference (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    RhoCostLayerConfiguration where
  normalizeOpen := rhoCIGSLT.costNormalizeOpen
  laws := laws.toCompactOpenNormalizerLaws

/-- The repaired hereditary executor as a point in the same parameterized
family.  The law bundle remains explicit, so this definition cannot be used
before the actual hereditary object theorem is constructed. -/
def hereditary
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditary) : RhoCostLayerConfiguration where
  normalizeOpen := rhoCostNormalizeOpenHereditary
  laws := laws

@[simp]
theorem reference_source
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    (reference laws).source = rhoReferenceCostLayer laws :=
  rfl

@[simp]
theorem hereditary_source
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditary) :
    (hereditary laws).source =
      rhoCIGSLT.costCIGSLTWith rhoCostNormalizeOpenHereditary laws :=
  rfl

end RhoCostLayerConfiguration

/-- The sole representative-shape premise used by the second-layer
obstruction.  It is intentionally local: an empty parallel occurring in any
boundary context must still normalize to rho's first-layer base unit.  No
claim is made that two arbitrary first-layer normalizers agree. -/
def RhoEmptyParallelSourceRepresentative
    (configuration : RhoCostLayerConfiguration) : Prop :=
  ∀ {color : CostStaticColor}
    (node : CostStaticRegionNode configuration.source color
      FreeTypeContext.empty),
    node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc →
      node.sourceBound = [] →
      (.collection .hashBag [] none : Pattern) = node.skeleton.1 →
      (configuration.source.openCanonical.normalize node.skeleton).1 =
        .apply (costBaseConstructorName "PZero") []

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
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) := by
  refine ⟨.collection .hashBag [] none, ⟨?_, rfl, rfl, rfl⟩, ?_⟩
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
  CostStaticRegionNode.ofPlan rhoBaseEmpty.toCore rhoBaseEmptyPlan rfl

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
    (configuration : RhoCostLayerConfiguration) :
    baseParallelRule ∈
      configuration.source.theory.presentation.presentation.language.terms :=
  rhoCIGSLT.costBaseConstructor_mem_costWhole rhoCalc.terms[3]
    rhoParallelRule_mem

private theorem baseParallelRule_wrapped
    (configuration : RhoCostLayerConfiguration) :
    baseParallelRule.label ∈
      (configuration.source).continuationRetyping.wrappedLabels := by
  apply (configuration.source).bareCollectionConstructorsWrapped baseParallelRule
  · exact baseParallelRule_mem configuration
  · change ∃ parameterName collectionType elementType,
      baseParallelRule.params =
        [.simple parameterName (.collection collectionType elementType)]
    exact ⟨"ps", .hashBag, .base (costBaseSortName "Proc"),
      rho_costBaseParallelConstructor_params⟩

private theorem baseParallelRule_noninteracting
    (configuration : RhoCostLayerConfiguration) :
    baseParallelRule.category ≠
      (configuration.source).theory.presentation.interactingSort.1.name :=
  costBaseSortName_ne_wrapped "Proc"

private theorem baseParallelRule_params :
    baseParallelRule.params =
      [.simple "ps"
        (.collection .hashBag (.base (costBaseSortName "Proc")))] :=
  rho_costBaseParallelConstructor_params

private def sourceSort (configuration : RhoCostLayerConfiguration) :
    LangSort (configuration.source).theory.presentation.presentation.language :=
  ⟨baseParallelRule.category,
    Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.termCategory_mem_of_validate_eq_nil
      _ (configuration.source).theory.presentation.presentation.valid _
        (baseParallelRule_mem configuration)⟩

private def parallelChoice : CostCollectionTypingChoice :=
  .bare baseParallelRule (.base (costBaseSortName "Proc"))

/-- The same declaration-derived empty parallel choice occurs in both
second-layer static colours. -/
theorem emptyParallelChoice_crossColorFor
    (configuration : RhoCostLayerConfiguration) :
    let source := configuration.source
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
    (configuration.source) FreeTypeContext.empty [] .hashBag baseParallelRule
      (.base (costBaseSortName "Proc")) (baseParallelRule_mem configuration)
      (baseParallelRule_wrapped configuration)
      (baseParallelRule_noninteracting configuration) "ps" baseParallelRule_params

/-- The reference first-layer executor inherits the declaration-derived
cross-colour choice.  This implication records the old API boundary; rho's
reference law premise is refuted independently. -/
theorem referenceEmptyParallelChoice_crossColor
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    let source := rhoReferenceCostLayer laws
    let expected :=
      mapTypeExpr (CostStaticColor.base.symbols source)
        (.base baseParallelRule.category)
    parallelChoice ∈
        costStaticCollectionTypingChoices source .base
          FreeTypeContext.empty [] .hashBag [] expected ∧
      parallelChoice ∈
        costStaticCollectionTypingChoices source .wrapped
          FreeTypeContext.empty [] .hashBag [] expected := by
  exact emptyParallelChoice_crossColorFor
    (RhoCostLayerConfiguration.reference laws)

private theorem baseChoice_mem
    (configuration : RhoCostLayerConfiguration) :
    parallelChoice ∈
      costStaticCollectionTypingChoices (configuration.source) .base
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols (configuration.source))
          (.base (sourceSort configuration).1)) :=
  (emptyParallelChoice_crossColorFor configuration).1

private theorem wrappedChoice_mem
    (configuration : RhoCostLayerConfiguration) :
    parallelChoice ∈
      costStaticCollectionTypingChoices (configuration.source) .wrapped
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.wrapped.symbols (configuration.source))
          (.base (sourceSort configuration).1)) := by
  have overlap :=
    (CostStaticColor.mapTypeExpr_base_eq_wrapped_iff
      (configuration.source) (.base (sourceSort configuration).1)).2 (by
        simpa [sourceSort, TypeExpr.baseNames] using
          (fun equality =>
            baseParallelRule_noninteracting configuration equality.symm))
  rw [← overlap]
  exact (emptyParallelChoice_crossColorFor configuration).2

private def basePlan (configuration : RhoCostLayerConfiguration) :
    CostStaticRegionPlan (configuration.source) .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget
        (configuration.source) .base [])
      [] (CostStaticBinderThinning.ofTargetThinning
        (configuration.source) .base [])
      [] .hole (.collection .hashBag [] none)
      (.base (sourceSort configuration).1) :=
  .collection parallelChoice (baseChoice_mem configuration) .nil

private def wrappedPlan (configuration : RhoCostLayerConfiguration) :
    CostStaticRegionPlan (configuration.source) .wrapped FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget
        (configuration.source) .wrapped [])
      [] (CostStaticBinderThinning.ofTargetThinning
        (configuration.source) .wrapped [])
      [] .hole (.collection .hashBag [] none)
      (.base (sourceSort configuration).1) :=
  .collection parallelChoice (wrappedChoice_mem configuration) .nil

private theorem nextBaseParallelRule_params
    (configuration : RhoCostLayerConfiguration) :
    (costBaseConstructor (configuration.source).cut baseParallelRule).params =
      [.simple "ps"
        (.collection .hashBag
          (mapTypeExpr (CostStaticColor.base.symbols (configuration.source))
            (.base (costBaseSortName "Proc"))))] := by
  rw [costBaseConstructor_params_eq_map_of_mem_wrappedLabels
    (configuration.source) baseParallelRule (baseParallelRule_mem configuration)
      (baseParallelRule_wrapped configuration), baseParallelRule_params]
  rfl

private theorem emptyParallel_typed
    (configuration : RhoCostLayerConfiguration) :
    HasType (configuration.source).costWholeLanguage FreeTypeContext.empty []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (configuration.source) (sourceSort configuration)).1) := by
  have typed :
      HasType (configuration.source).costWholeLanguage FreeTypeContext.empty []
        (.collection .hashBag [] none)
        (.base
          (costBaseConstructor
            (configuration.source).cut baseParallelRule).category) := by
    apply HasType.collectionConstructor
        (rule := costBaseConstructor (configuration.source).cut baseParallelRule)
        (parameterName := "ps")
        (elementType :=
          mapTypeExpr (CostStaticColor.base.symbols (configuration.source))
            (.base (costBaseSortName "Proc")))
    · exact (configuration.source).costBaseConstructor_mem_costWhole
        baseParallelRule (baseParallelRule_mem configuration)
    · exact nextBaseParallelRule_params configuration
    · exact .nil [] _
  simpa [sourceSort, CostStaticColor.symbols, costBaseStaticSymbols,
    costBaseLanguageDefSymbolMap, costBaseConstructor] using typed

private def emptyParallel
    (configuration : RhoCostLayerConfiguration) :
    ReflectiveWellSorted.OpenTerm
      (configuration.source).costWholeReflectionProfile
      (configuration.source).costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort
        (configuration.source) (sourceSort configuration)) := by
  refine ⟨.collection .hashBag [] none,
    ⟨emptyParallel_typed configuration, rfl, rfl, rfl⟩, ?_⟩
  intro declaration membership
  rfl

private theorem colorOverlap
    (configuration : RhoCostLayerConfiguration) :
    CostStaticColor.base.mapLangSort (configuration.source) (sourceSort configuration) =
      CostStaticColor.wrapped.mapLangSort
        (configuration.source) (sourceSort configuration) :=
  (CostStaticColor.mapLangSort_base_eq_wrapped_iff
    (configuration.source) (sourceSort configuration)).2
      (baseParallelRule_noninteracting configuration)

private def wrappedEmptyParallel
    (configuration : RhoCostLayerConfiguration) :
    ReflectiveWellSorted.OpenTerm
      (configuration.source).costWholeReflectionProfile
      (configuration.source).costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.wrapped.mapLangSort
        (configuration.source) (sourceSort configuration)) :=
  ReflectiveWellSorted.OpenTerm.reindex rfl rfl (colorOverlap configuration)
    (emptyParallel configuration)

private def baseNode
    (configuration : RhoCostLayerConfiguration) :
    CostStaticRegionNode (configuration.source) .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan (emptyParallel configuration).toCore (basePlan configuration) rfl

private def wrappedNode
    (configuration : RhoCostLayerConfiguration) :
    CostStaticRegionNode (configuration.source) .wrapped FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan
    (wrappedEmptyParallel configuration).toCore (wrappedPlan configuration) rfl

private theorem baseNode_sourceSort
    (configuration : RhoCostLayerConfiguration) :
    (baseNode configuration).sourceSort =
      CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc := by
  apply Subtype.ext
  rfl

private theorem baseNode_sourceBound
    (configuration : RhoCostLayerConfiguration) :
    (baseNode configuration).sourceBound = [] := by
  change
    CostStaticBinderThinning.sourceContextOfTarget (configuration.source) .base
      (baseNode configuration).targetBound = []
  rw [show (baseNode configuration).targetBound = [] by rfl]
  simp [CostStaticBinderThinning.sourceContextOfTarget]

private theorem wrappedNode_sourceSort
    (configuration : RhoCostLayerConfiguration) :
    (wrappedNode configuration).sourceSort =
      CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc := by
  apply Subtype.ext
  rfl

private theorem wrappedNode_sourceBound
    (configuration : RhoCostLayerConfiguration) :
    (wrappedNode configuration).sourceBound = [] := by
  change
    CostStaticBinderThinning.sourceContextOfTarget (configuration.source) .wrapped
      (wrappedNode configuration).targetBound = []
  rw [show (wrappedNode configuration).targetBound = [] by rfl]
  simp [CostStaticBinderThinning.sourceContextOfTarget]

private theorem baseNode_skeleton_pattern_eq
    (configuration : RhoCostLayerConfiguration) :
    (.collection .hashBag [] none : Pattern) =
      (baseNode configuration).skeleton.1 := by
  rfl

private theorem wrappedNode_skeleton_pattern_eq
    (configuration : RhoCostLayerConfiguration) :
    (.collection .hashBag [] none : Pattern) =
      (wrappedNode configuration).skeleton.1 := by
  rfl

private theorem rhoParallelChoice_memAt
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
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
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
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
  .collection rhoParallelChoice (rhoParallelChoice_memAt configuration node) .nil

private def rhoBaseEmptyAt
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
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
  · rfl

private def rhoBaseEmptyNodeAt
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty) :
    CostStaticRegionNode rhoCIGSLT .base
      node.boundaryTable.sourceFreeContext :=
  CostStaticRegionNode.ofPlan (rhoBaseEmptyAt configuration node)
    (rhoBaseEmptyPlanAt configuration node) rfl

private def rhoBaseEmptyTreeAt
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty) :
    CostRegionTree rhoCIGSLT
      node.boundaryTable.sourceFreeContext
      node.sourceBound []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc).1) :=
  .static (rhoBaseEmptyNodeAt configuration node) .nil

private theorem sourceNode_sourceType_eq
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
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
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    CostOpenElaboration rhoCIGSLT node.skeleton :=
  ⟨((rhoBaseEmptyTreeAt configuration node).reindexType
      (sourceNode_sourceType_eq configuration node sourceSortEq)).reindexPattern
        patternEq⟩

private theorem rhoBaseEmptyElaborationAt_normalize_eq
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    (rhoBaseEmptyElaborationAt configuration node sourceSortEq
      patternEq).tree.normalize.pattern =
      (rhoBaseEmptyTreeAt configuration node).normalize.pattern := by
  exact (CostRegionTree.reindexPattern_normalize
    (patternEq := patternEq)
    (tree := (rhoBaseEmptyTreeAt configuration node).reindexType
      (sourceNode_sourceType_eq configuration node sourceSortEq))).trans
        (CostRegionTree.reindexType_normalize
          (typeEq := sourceNode_sourceType_eq configuration node sourceSortEq)
          (tree := rhoBaseEmptyTreeAt configuration node))

private theorem rhoBaseEmptyNodeAt_normalizedThickenedSkeletonRaw
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty)
    (sourceBoundEq : node.sourceBound = []) :
    (rhoBaseEmptyNodeAt configuration node).normalizedThickenedSkeletonRaw =
      .apply (costBaseConstructorName "PZero") [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (rhoBaseEmptyNodeAt configuration node).thinning sourceBoundEq]
  unfold normalizeCostStaticStratum
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (rhoBaseEmptyNodeAt configuration node).skeleton.1) =
    _
  rw [(rhoBaseEmptyNodeAt configuration node).skeleton_pattern]
  change mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (.collection .hashBag [] none)) =
    _
  rw [
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_parallel_empty]
  rfl

private theorem rhoBaseEmptyElaborationAt_normalized_pattern
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (sourceBoundEq : node.sourceBound = [])
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    (rhoBaseEmptyElaborationAt configuration node sourceSortEq
      patternEq).normalizeErasure.1 =
      .apply (costBaseConstructorName "PZero") [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  rw [rhoBaseEmptyElaborationAt_normalize_eq configuration node sourceSortEq patternEq]
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (rhoBaseEmptyNodeAt configuration node) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    rhoBaseEmptyNodeAt_normalizedThickenedSkeletonRaw configuration node sourceBoundEq]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

private theorem referenceSourceNode_sourceCanonical
    {color : CostStaticColor}
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    ∀ (node : CostStaticRegionNode
        (RhoCostLayerConfiguration.reference laws).source color
        FreeTypeContext.empty)
      (_sourceSortEq :
        node.sourceSort =
          CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
      (_sourceBoundEq : node.sourceBound = [])
      (_patternEq : (.collection .hashBag [] none : Pattern) =
        node.skeleton.1),
      ((RhoCostLayerConfiguration.reference laws).source.openCanonical.normalize
        node.skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] := by
  intro node _sourceSortEq _sourceBoundEq _patternEq
  change (rhoCIGSLT.costNormalizeOpen node.skeleton).1 = _
  calc
    (rhoCIGSLT.costNormalizeOpen node.skeleton).1 =
        (CostOpenElaboration.compile rhoCIGSLT
          node.skeleton).normalizeErasure.1 := rfl
    _ = (rhoBaseEmptyElaborationAt
          (RhoCostLayerConfiguration.reference laws) node _sourceSortEq
          _patternEq).normalizeErasure.1 :=
      congrArg (fun term => term.1)
        (CostCanonicalLaws.rho_compactCostNormalizationCoherent node.skeleton
          (CostOpenElaboration.compile rhoCIGSLT
            node.skeleton)
          (rhoBaseEmptyElaborationAt
            (RhoCostLayerConfiguration.reference laws) node _sourceSortEq
              _patternEq))
    _ = _ := rhoBaseEmptyElaborationAt_normalized_pattern
      (RhoCostLayerConfiguration.reference laws) node
      _sourceSortEq _sourceBoundEq _patternEq

/-- The reference rho normalizer would satisfy the representative fact needed
by the parameterized cost-layer iteration obstruction.  Its law premise is independently
refuted for rho. -/
theorem reference_emptyParallelSourceRepresentative
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    RhoEmptyParallelSourceRepresentative
      (RhoCostLayerConfiguration.reference laws) := by
  intro color node sourceSortEq sourceBoundEq patternEq
  exact referenceSourceNode_sourceCanonical laws node sourceSortEq
    sourceBoundEq patternEq

private theorem rhoBaseEmptyElaborationAt_normalizedHereditary_pattern
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (node : CostStaticRegionNode (configuration.source) color
      FreeTypeContext.empty)
    (sourceSortEq :
      node.sourceSort =
        CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
    (sourceBoundEq : node.sourceBound = [])
    (patternEq : (.collection .hashBag [] none : Pattern) =
      node.skeleton.1) :
    (CostRegionTree.normalizeHereditary
      (rhoBaseEmptyElaborationAt configuration node sourceSortEq
        patternEq).tree).pattern =
      .apply (costBaseConstructorName "PZero") [] := by
  have staticResult :
      ((rhoBaseEmptyTreeAt configuration node).normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        .apply (costBaseConstructorName "PZero") [] := by
    let emptyChildren : CostRegionBoundaryTrees rhoCIGSLT
        node.boundaryTable.sourceFreeContext .base
        (rhoBaseEmptyNodeAt configuration node).finiteBoundaryTable := .nil
    have valuesEq :=
      CostRegionBoundaryTrees.normalizeValues_eq_original_of_entries_eq_nil
        (source := rhoCIGSLT) rhoHereditaryStaticNormalizer
        emptyChildren
        (by rfl)
    calc
      _ = (rhoHereditaryStaticNormalizer
            (rhoBaseEmptyNodeAt configuration node)
            (emptyChildren.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1 :=
        CostRegionTree.normalize_static_pattern
          rhoHereditaryStaticNormalizer
          (rhoBaseEmptyNodeAt configuration node) emptyChildren
      _ = (rhoHereditaryStaticNormalizer
            (rhoBaseEmptyNodeAt configuration node)
            (TypedCostRegionBoundaryTable.Values.original
              (rhoBaseEmptyNodeAt configuration node).finiteBoundaryTable)
            ).1 := congrArg (fun values =>
              (rhoHereditaryStaticNormalizer
                (rhoBaseEmptyNodeAt configuration node) values).1) valuesEq
      _ = _ := by
        let emptyNode := rhoBaseEmptyNodeAt configuration node
        let values := TypedCostRegionBoundaryTable.Values.original
          emptyNode.finiteBoundaryTable
        let inventory := (emptyNode.semanticAtomEnvironment values).1
        let environment := CostStaticAtomEnvironment.ofInventory inventory
        have targetBoundEq : emptyNode.targetBound = [] := by
          change node.sourceBound = []
          exact sourceBoundEq
        have reifiedFrame :
            (emptyNode.reifiedSourceFrame environment).1 =
              .collection .hashBag [] none := by
          rw [CostStaticRegionNode.reifiedSourceFrame_pattern]
          change environment.reify (.collection .hashBag [] none) = _
          simp [CostStaticAtomEnvironment.reify]
        change (CostStaticRegionNode.normalizeHereditary emptyNode values).1 = _
        unfold CostStaticRegionNode.normalizeHereditary
        rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
        rw [CostStaticRegionNode.normalizeHereditaryRawWithInventory_eq_sourceAction]
        rw [reifiedFrame]
        simp only [canonicalizeByDepths, canonicalizeListByDepths,
          normalizeParallelElementsBy, sortPatternsBy,
          List.flatMap_nil, List.filter_nil, List.mergeSort_nil,
          collapseParallel]
        unfold CostCanonicalLaws.rhoCostStaticActionAt
        rw [
          CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
            emptyNode.thinning targetBoundEq]
        simp [rhoReflectivePresentation, CostStaticColor.symbols,
          costBaseStaticSymbols, costBaseLanguageDefSymbolMap, mapPattern,
          ReflectiveContextSupport.substituteAt]
  unfold CostRegionTree.normalizeHereditary
  calc
    _ = (((rhoBaseEmptyTreeAt configuration node).reindexType
          (sourceNode_sourceType_eq configuration node sourceSortEq)).normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
      CostRegionTree.reindexPattern_normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer) patternEq
        ((rhoBaseEmptyTreeAt configuration node).reindexType
          (sourceNode_sourceType_eq configuration node sourceSortEq))
    _ = ((rhoBaseEmptyTreeAt configuration node).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
      CostRegionTree.reindexType_normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)
        (sourceNode_sourceType_eq configuration node sourceSortEq)
        (rhoBaseEmptyTreeAt configuration node)
    _ = _ := staticResult

private theorem hereditarySourceNode_sourceCanonical
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditary)
    {color : CostStaticColor} :
    ∀ (node : CostStaticRegionNode
        (RhoCostLayerConfiguration.hereditary laws).source color
        FreeTypeContext.empty)
      (_sourceSortEq :
        node.sourceSort =
          CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
      (_sourceBoundEq : node.sourceBound = [])
      (_patternEq : (.collection .hashBag [] none : Pattern) =
        node.skeleton.1),
      ((RhoCostLayerConfiguration.hereditary laws).source.openCanonical.normalize
        node.skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] := by
  intro node _sourceSortEq _sourceBoundEq _patternEq
  change (rhoCostNormalizeOpenHereditary node.skeleton).1 = _
  calc
    (rhoCostNormalizeOpenHereditary node.skeleton).1 =
        (CostRegionTree.normalizeHereditary
          (CostRegionTree.buildOpenTerm (source := rhoCIGSLT)
            node.skeleton)).pattern := rfl
    _ = (CostRegionTree.normalizeHereditary
          (rhoBaseEmptyElaborationAt
            (RhoCostLayerConfiguration.hereditary laws) node _sourceSortEq
              _patternEq).tree).pattern :=
      (CostRegionTree.normalizeHereditary_eq_buildOpenTerm node.skeleton
        (rhoBaseEmptyElaborationAt
          (RhoCostLayerConfiguration.hereditary laws) node _sourceSortEq
            _patternEq).tree).symm
    _ = _ := rhoBaseEmptyElaborationAt_normalizedHereditary_pattern
      (RhoCostLayerConfiguration.hereditary laws) node _sourceSortEq
        _sourceBoundEq _patternEq

/-- The hereditary rho executor satisfies the exact representative premise
used by the parameterized cost-layer iteration obstruction. -/
theorem hereditary_emptyParallelSourceRepresentative
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditary) :
    RhoEmptyParallelSourceRepresentative
      (RhoCostLayerConfiguration.hereditary laws) := by
  intro color node sourceSortEq sourceBoundEq patternEq
  exact hereditarySourceNode_sourceCanonical laws node sourceSortEq
    sourceBoundEq patternEq

/-- The canonical closed empty-parallel input used to identify a selected
first-layer rho executor. -/
def rhoBaseEmptyRepresentative :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) :=
  rhoBaseEmpty

/-- The raw hereditary executor selects rho's base unit on the canonical
closed empty-parallel input. -/
theorem rhoCostNormalizeOpenHereditary_baseEmptyRepresentative :
    (rhoCostNormalizeOpenHereditary rhoBaseEmptyRepresentative).1 =
      .apply (costBaseConstructorName "PZero") [] := by
  change (CostRegionTree.normalizeHereditary rhoBaseEmptyTree).pattern = _
  let emptyChildren : CostRegionBoundaryTrees rhoCIGSLT
      FreeTypeContext.empty .base
      rhoBaseEmptyNode.finiteBoundaryTable := .nil
  have valuesEq :=
    CostRegionBoundaryTrees.normalizeValues_eq_original_of_entries_eq_nil
      (source := rhoCIGSLT) rhoHereditaryStaticNormalizer emptyChildren
      (by rfl)
  change (rhoBaseEmptyTree.normalize
    (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = _
  calc
    _ = (rhoHereditaryStaticNormalizer rhoBaseEmptyNode
          (emptyChildren.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
      change ((CostRegionTree.static (outer := []) rhoBaseEmptyNode
        emptyChildren).normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern = _
      exact CostRegionTree.normalize_static_pattern
        rhoHereditaryStaticNormalizer rhoBaseEmptyNode emptyChildren
    _ = (rhoHereditaryStaticNormalizer rhoBaseEmptyNode
          (TypedCostRegionBoundaryTable.Values.original
            rhoBaseEmptyNode.finiteBoundaryTable)).1 :=
      congrArg (fun values =>
        (rhoHereditaryStaticNormalizer rhoBaseEmptyNode values).1) valuesEq
    _ = _ := by
      let values := TypedCostRegionBoundaryTable.Values.original
        rhoBaseEmptyNode.finiteBoundaryTable
      let inventory := (rhoBaseEmptyNode.semanticAtomEnvironment values).1
      let environment := CostStaticAtomEnvironment.ofInventory inventory
      have reifiedFrame :
          (rhoBaseEmptyNode.reifiedSourceFrame environment).1 =
            .collection .hashBag [] none := by
        rw [CostStaticRegionNode.reifiedSourceFrame_pattern]
        change environment.reify (.collection .hashBag [] none) = _
        simp [CostStaticAtomEnvironment.reify]
      change (CostStaticRegionNode.normalizeHereditary rhoBaseEmptyNode
        values).1 = _
      unfold CostStaticRegionNode.normalizeHereditary
      rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
      rw [CostStaticRegionNode.normalizeHereditaryRawWithInventory_eq_sourceAction]
      rw [reifiedFrame]
      simp only [canonicalizeByDepths, canonicalizeListByDepths,
        normalizeParallelElementsBy, sortPatternsBy,
        List.flatMap_nil, List.filter_nil, List.mergeSort_nil,
        collapseParallel]
      unfold CostCanonicalLaws.rhoCostStaticActionAt
      rw [CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
        rhoBaseEmptyNode.thinning rfl]
      simp [rhoReflectivePresentation, CostStaticColor.symbols,
        costBaseStaticSymbols, costBaseLanguageDefSymbolMap, mapPattern,
        ReflectiveContextSupport.substituteAt]

/-- A lawful selected first-layer executor has the required representative
as soon as it chooses rho's base unit on the single canonical closed empty
parallel.  Contextual naturality transports that value to every reconstructed
boundary context used by the second-layer witness. -/
theorem emptyParallelSourceRepresentative_of_baseEmptyRepresentative
    (configuration : RhoCostLayerConfiguration)
    (selectsBaseEmpty :
      (configuration.normalizeOpen rhoBaseEmptyRepresentative).1 =
        .apply (costBaseConstructorName "PZero") []) :
    RhoEmptyParallelSourceRepresentative configuration := by
  intro color node sourceSortEq sourceBoundEq patternEq
  change (configuration.normalizeOpen node.skeleton).1 = _
  have boundEquality : ([] : List TypeExpr) = node.sourceBound :=
    sourceBoundEq.symm
  have sortEquality :
      CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc = node.sourceSort :=
    sourceSortEq.symm
  have preserves : ∀ {name freeType},
      name ∈ rhoBaseEmptyRepresentative.1.freeFvarNames →
      FreeTypeContext.empty name = some freeType →
        node.boundaryTable.sourceFreeContext name = some freeType := by
    intro name freeType _membership lookup
    simp [FreeTypeContext.empty] at lookup
  let contextualized :=
    rhoBaseEmptyRepresentative.recontextualizeFree preserves
  let transported := contextualized.reindex rfl boundEquality sortEquality
  have transportedPattern : transported.1 = node.skeleton.1 := by
    calc
      transported.1 = contextualized.1 := by
        unfold transported
        exact ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _
      _ = rhoBaseEmptyRepresentative.1 :=
        ReflectiveWellSorted.OpenTerm.recontextualizeFree_pattern _ _
      _ = (.collection .hashBag [] none : Pattern) := rfl
      _ = node.skeleton.1 := patternEq
  have transportedTerm : transported = node.skeleton := by
    apply Subtype.ext
    exact transportedPattern
  have normalizedReindex :
      configuration.source.openCanonical.normalize transported =
        (configuration.source.openCanonical.normalize contextualized).reindex
          rfl boundEquality sortEquality := by
    unfold transported
    exact configuration.source.openCanonical.normalize_reindex rfl
      boundEquality sortEquality contextualized
  have normalizedTransported :
      (configuration.normalizeOpen transported).1 =
        (configuration.normalizeOpen contextualized).1 := by
    change
      (configuration.source.openCanonical.normalize transported).1 =
        (configuration.source.openCanonical.normalize contextualized).1
    calc
      _ = ((configuration.source.openCanonical.normalize contextualized
            ).reindex rfl boundEquality sortEquality).1 :=
        congrArg (fun term => term.1) normalizedReindex
      _ = _ := ReflectiveWellSorted.OpenTerm.reindex_pattern _ _ _ _
  have normalizedContextualized :
      (configuration.normalizeOpen contextualized).1 =
        (configuration.normalizeOpen rhoBaseEmptyRepresentative).1 := by
    exact configuration.laws.normalizeRecontextualizeFree
      rhoBaseEmptyRepresentative preserves
  calc
    (configuration.normalizeOpen node.skeleton).1 =
        (configuration.normalizeOpen transported).1 := by
      exact (congrArg (fun term =>
        (configuration.normalizeOpen term).1) transportedTerm).symm
    _ = (configuration.normalizeOpen contextualized).1 :=
      normalizedTransported
    _ = (configuration.normalizeOpen rhoBaseEmptyRepresentative).1 :=
      normalizedContextualized
    _ = _ := selectsBaseEmpty

private theorem sourceNode_sourceCanonical
    {color : CostStaticColor}
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    ∀ (node : CostStaticRegionNode configuration.source color
        FreeTypeContext.empty)
      (_sourceSortEq :
        node.sourceSort =
          CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc)
      (_sourceBoundEq : node.sourceBound = [])
      (_patternEq : (.collection .hashBag [] none : Pattern) =
        node.skeleton.1),
      (configuration.source.openCanonical.normalize node.skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] := by
  intro node sourceSortEq sourceBoundEq patternEq
  exact representative node sourceSortEq sourceBoundEq patternEq

private theorem baseNode_sourceCanonical
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    ((configuration.source).openCanonical.normalize
      (baseNode configuration).skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] :=
  sourceNode_sourceCanonical configuration representative
    (baseNode configuration)
    (baseNode_sourceSort configuration) (baseNode_sourceBound configuration)
      (baseNode_skeleton_pattern_eq configuration)

private theorem wrappedNode_sourceCanonical
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    ((configuration.source).openCanonical.normalize
      (wrappedNode configuration).skeleton).1 =
        .apply (costBaseConstructorName "PZero") [] :=
  sourceNode_sourceCanonical configuration representative
    (wrappedNode configuration)
    (wrappedNode_sourceSort configuration) (wrappedNode_sourceBound configuration)
      (wrappedNode_skeleton_pattern_eq configuration)

private theorem baseNode_normalizedThickenedSkeletonRaw
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    (baseNode configuration).normalizedThickenedSkeletonRaw =
      .apply
        (costBaseConstructorName (costBaseConstructorName "PZero")) [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (baseNode configuration).thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [baseNode_sourceCanonical configuration representative]
  rfl

private theorem wrappedNode_normalizedThickenedSkeletonRaw
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    (wrappedNode configuration).normalizedThickenedSkeletonRaw =
      .apply
        (costWrappedConstructorName (costBaseConstructorName "PZero")) [] := by
  unfold CostStaticRegionNode.normalizedThickenedSkeletonRaw
  rw [
    CostStaticBinderThinning.thickenAmbientBVars_eq_self_of_targetBound_eq_nil
      (wrappedNode configuration).thinning (by rfl)]
  unfold normalizeCostStaticStratum
  rw [wrappedNode_sourceCanonical configuration representative]
  rfl

private def baseTree
    (configuration : RhoCostLayerConfiguration) :
    CostRegionTree (configuration.source) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (configuration.source) (sourceSort configuration)).1) :=
  .static (baseNode configuration) .nil

private def wrappedTreeNatural
    (configuration : RhoCostLayerConfiguration) :
    CostRegionTree (configuration.source) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.wrapped.mapLangSort
        (configuration.source) (sourceSort configuration)).1) :=
  .static (wrappedNode configuration) .nil

private theorem colorOverlapType
    (configuration : RhoCostLayerConfiguration) :
    (.base (CostStaticColor.wrapped.mapLangSort
      (configuration.source) (sourceSort configuration)).1 : TypeExpr) =
    .base (CostStaticColor.base.mapLangSort
      (configuration.source) (sourceSort configuration)).1 :=
  congrArg (fun sort : LangSort (configuration.source).costWholeLanguage =>
    (.base sort.1 : TypeExpr)) (colorOverlap configuration).symm

private def wrappedTree
    (configuration : RhoCostLayerConfiguration) :
    CostRegionTree (configuration.source) FreeTypeContext.empty [] []
      (.collection .hashBag [] none)
      (.base (CostStaticColor.base.mapLangSort
        (configuration.source) (sourceSort configuration)).1) := by
  exact (wrappedTreeNatural configuration).reindexType (colorOverlapType configuration)

private theorem wrappedTree_normalize_eq
    (configuration : RhoCostLayerConfiguration) :
    (wrappedTree configuration).normalize.pattern =
      (wrappedTreeNatural configuration).normalize.pattern :=
  CostRegionTree.reindexType_normalize
    (typeEq := colorOverlapType configuration) (tree := wrappedTreeNatural configuration)

private def baseElaboration
    (configuration : RhoCostLayerConfiguration) :
    CostOpenElaboration (configuration.source) (emptyParallel configuration) :=
  ⟨baseTree configuration⟩

private def wrappedElaboration
    (configuration : RhoCostLayerConfiguration) :
    CostOpenElaboration (configuration.source) (emptyParallel configuration) :=
  ⟨wrappedTree configuration⟩

private theorem base_normalized_pattern
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    (baseElaboration configuration).normalizeErasure.1 =
      .apply
        (costBaseConstructorName (costBaseConstructorName "PZero")) [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  change (baseTree configuration).normalize.pattern = _
  unfold baseTree
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (baseNode configuration) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    baseNode_normalizedThickenedSkeletonRaw configuration representative]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

private theorem wrapped_normalized_pattern
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    (wrappedElaboration configuration).normalizeErasure.1 =
      .apply
        (costWrappedConstructorName (costBaseConstructorName "PZero")) [] := by
  rw [CostOpenElaboration.normalizeErasure_pattern]
  change (wrappedTree configuration).normalize.pattern = _
  rw [wrappedTree_normalize_eq configuration]
  unfold wrappedTreeNatural
  apply Eq.trans
    (CostRegionTree.normalize_static_eq_normalizeRaw_of_entries_eq_nil
      (wrappedNode configuration) .nil (by rfl))
  unfold CostStaticRegionNode.normalizeRaw
    CostStaticRegionNode.normalizeRawWith
  rw [CostStaticRegionNode.normalizedThickenedSkeleton_pattern,
    wrappedNode_normalizedThickenedSkeletonRaw configuration representative]
  simp [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, ReflectiveContextSupport.substituteAt]

/-- Exact compact coherence is not closed by a second Cost application on
rho.  The same checked compact empty parallel has base- and wrapped-colour
elaborations whose normalized units retain distinct constructor identities. -/
theorem rhoCostLayerFor_not_compactCostNormalizationCoherent
    (configuration : RhoCostLayerConfiguration)
    (representative : RhoEmptyParallelSourceRepresentative configuration) :
    ¬ CompactCostNormalizationCoherent (configuration.source) := by
  intro coherent
  have equal :=
    congrArg (fun term => term.1)
      (coherent (emptyParallel configuration)
        (baseElaboration configuration) (wrappedElaboration configuration))
  rw [base_normalized_pattern configuration representative,
    wrapped_normalized_pattern configuration representative] at equal
  have labelsEqual :
      costBaseConstructorName (costBaseConstructorName "PZero") =
        costWrappedConstructorName (costBaseConstructorName "PZero") := by
    injection equal
  exact costBaseConstructorName_ne_wrapped
    (costBaseConstructorName "PZero")
    (costBaseConstructorName "PZero") labelsEqual

/-- The reference-executor obstruction is the corresponding implication from
the old, refuted rho object premise.  The normalizer-parameterized theorem
above and its hereditary instance carry the substantive cost-layer iteration boundary. -/
theorem rhoReferenceCostLayer_not_compactCostNormalizationCoherent
    (laws : Cost.ReferenceCompactOpenNormalizer.Laws rhoCIGSLT) :
    ¬ CompactCostNormalizationCoherent (rhoReferenceCostLayer laws) := by
  exact rhoCostLayerFor_not_compactCostNormalizationCoherent
    (RhoCostLayerConfiguration.reference laws)
    (reference_emptyParallelSourceRepresentative laws)

/-- The repaired hereditary executor meets the same precise cost-layer iteration boundary:
its first layer is a genuine Cost object, while its generated compact syntax
does not support a second exact compact section. -/
theorem rhoHereditaryCostLayer_not_compactCostNormalizationCoherent
    (laws : Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditary) :
    ¬ CompactCostNormalizationCoherent
      (rhoCIGSLT.costCIGSLTWith rhoCostNormalizeOpenHereditary laws) := by
  exact rhoCostLayerFor_not_compactCostNormalizationCoherent
    (RhoCostLayerConfiguration.hereditary laws)
    (hereditary_emptyParallelSourceRepresentative laws)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostIterationObstruction
