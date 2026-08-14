import Mettapedia.GSLT.LanguageDef.CostElaborationPlanReindex
import Mettapedia.GSLT.LanguageDef.CostElaboratedCarrier

/-!
# Reindexing proof-relevant Cost region trees

Conservative Cost arrows preserve every structural decision retained by an
elaboration.  This module maps static nodes and recursive region trees without
rerunning the planner or quotienting repeated boundary occurrences.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory

namespace CostStaticRegionNode

/-- The smart constructor retains the supplied structural plan literally. -/
@[simp]
theorem ofPlan_plan {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {sourceSort : LangSort source.theory.presentation.presentation.language}
    (term : WellSorted.OpenTerm source.costWholeLanguage targetFree
      targetBound (color.mapLangSort source sourceSort))
    (plan : CostStaticRegionPlan source color targetFree
      (CostStaticBinderThinning.sourceContextOfTarget source color targetBound)
      targetBound
      (CostStaticBinderThinning.ofTargetThinning source color targetBound)
      targetBound .hole term.1 (.base sourceSort.1))
    (rootStatic : plan.isStaticRoot = true) :
    (CostStaticRegionNode.ofPlan term plan rootStatic).plan = plan :=
  rfl

/-- The authored source sort transported by the underlying continued map. -/
def mappedSourceSort {source target : CIGSLT}
    (morphism : source.Morphism target)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    LangSort target.theory.presentation.presentation.language :=
  WellSorted.mapLangSort morphism.underlying.structural.structural
    node.sourceSort

/-- The generated open term transported into the corresponding target
static fibre. -/
def mappedTerm {source target : CIGSLT}
    (morphism : source.Morphism target)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    WellSorted.OpenTerm target.costWholeLanguage
      (targetFree.map morphism.costWholeStructural.symbols)
      (node.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols))
      (color.mapLangSort target (node.mappedSourceSort morphism)) :=
  WellSorted.OpenTerm.reindex rfl rfl
    (morphism.mapLangSort_costStatic_natural color node.sourceSort)
    (node.term.map morphism.costWholeStructural)

@[simp]
theorem mappedTerm_pattern {source target : CIGSLT}
    (morphism : source.Morphism target)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.mappedTerm morphism).1 =
      mapPattern morphism.costWholeStructural.symbols node.term.1 := by
  exact (WellSorted.OpenTerm.reindex_pattern _ _ _
    (node.term.map morphism.costWholeStructural)).trans
      (WellSorted.OpenTerm.map_pattern morphism.costWholeStructural node.term)

/-- The sole structural plan transported to the target node indices. -/
def mappedPlan {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    CostStaticRegionPlan target color
      (targetFree.map morphism.costWholeStructural.symbols)
      (CostStaticBinderThinning.sourceContextOfTarget target color
        (node.targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols)))
      (node.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols))
      (CostStaticBinderThinning.ofTargetThinning target color
        (node.targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols)))
      (node.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols))
      .hole (node.mappedTerm morphism).1
      (.base (node.mappedSourceSort morphism).1) := by
  let rawPlan := mapCostStaticRegionPlan morphism scope laws node.plan
    node.term.2.2.2.1
  have sourceBoundEquality :
      (CostStaticBinderThinning.sourceContextOfTarget source color
          node.targetBound).map
          (mapTypeExpr
            morphism.underlying.structural.structural.symbols) =
        CostStaticBinderThinning.sourceContextOfTarget target color
          (node.targetBound.map
            (mapTypeExpr morphism.costWholeStructural.symbols)) :=
    (CostStaticBinderThinning.sourceContextOfTarget_natural morphism color
      node.targetBound).symm
  have outerEquality :
      CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
          OneHoleContext.hole = OneHoleContext.hole := by
    simp [CIGSLT.mapOneHoleContext]
  have patternEquality :
      mapPattern morphism.costWholeStructural.symbols node.term.1 =
        (node.mappedTerm morphism).1 :=
    (node.mappedTerm_pattern morphism).symm
  have sourceTypeEquality :
      mapTypeExpr morphism.underlying.structural.structural.symbols
          (.base node.sourceSort.1) =
        .base (node.mappedSourceSort morphism).1 := by
    rfl
  exact CostStaticRegionPlan.reindex
    (thinning₂ := CostStaticBinderThinning.ofTargetThinning target color
      (node.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols)))
    sourceBoundEquality rfl rfl outerEquality patternEquality
      sourceTypeEquality rawPlan

/-- Transporting a node plan preserves its maximal-static-root witness. -/
theorem mappedPlan_isStaticRoot {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.mappedPlan morphism scope laws).isStaticRoot = true := by
  unfold mappedPlan
  rw [CostStaticRegionPlan.reindex_isStaticRoot]
  exact (mapCostStaticRegionPlan_isStaticRoot morphism scope laws node.plan
    node.term.2.2.2.1).trans node.rootStatic

/-- Map one static node by transporting its sole structural plan and then
rebuilding all redundant node evidence through `ofPlan`. -/
def map {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    CostStaticRegionNode target color
      (targetFree.map morphism.costWholeStructural.symbols) :=
  CostStaticRegionNode.ofPlan (node.mappedTerm morphism)
    (node.mappedPlan morphism scope laws)
    (node.mappedPlan_isStaticRoot morphism scope laws)

/-- Mapping the retained plan maps the complete ordered boundary packet. -/
theorem mappedPlan_boundaryPacket {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.mappedPlan morphism scope laws).boundaryPacket =
      TypedCostRegionBoundaryPacket.map morphism scope color
        node.plan.boundaryPacket := by
  unfold mappedPlan
  rw [CostStaticRegionPlan.reindex_boundaryPacket]
  exact mapCostStaticRegionPlan_boundaryPacket morphism scope laws node.plan
    node.term.2.2.2.1

/-- Node reindexing retains the complete ordered boundary packet generated
by its source plan. -/
theorem map_boundaryPacket {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.map morphism scope laws).plan.boundaryPacket =
      TypedCostRegionBoundaryPacket.map morphism scope color
        node.plan.boundaryPacket := by
  rw [map, CostStaticRegionNode.ofPlan_plan]
  exact node.mappedPlan_boundaryPacket morphism scope laws

@[simp]
theorem map_targetBound {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.map morphism scope laws).targetBound =
      node.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols) :=
  rfl

@[simp]
theorem map_sourceSort {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.map morphism scope laws).sourceSort =
      node.mappedSourceSort morphism :=
  rfl

@[simp]
theorem map_term_pattern {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.map morphism scope laws).term.1 =
      mapPattern morphism.costWholeStructural.symbols node.term.1 := by
  rw [map]
  exact node.mappedTerm_pattern morphism

end CostStaticRegionNode

/-- Transport all five indices of a region tree along equalities.  No
decomposition data changes. -/
def CostRegionTree.reindex {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext}
    {available₁ available₂ outer₁ outer₂ : List TypeExpr}
    {pattern₁ pattern₂ : Pattern} {type₁ type₂ : TypeExpr}
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (type : type₁ = type₂)
    (tree : CostRegionTree source targetFree available₁ outer₁ pattern₁
      type₁) :
    CostRegionTree source targetFree available₂ outer₂ pattern₂
      type₂ := by
  subst available₂
  subst outer₂
  subst pattern₂
  subst type₂
  exact tree

/-- Transport a boundary forest along equality of its total occurrence/table
packet. -/
def CostRegionBoundaryTrees.reindexPacket {source : CIGSLT}
    {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
    {sourcePacket targetPacket :
      TypedCostRegionBoundaryPacket source color targetFree}
    (packet : sourcePacket = targetPacket)
    (trees : CostRegionBoundaryTrees source targetFree color sourcePacket.2) :
    CostRegionBoundaryTrees source targetFree color targetPacket.2 := by
  subst targetPacket
  exact trees

mutual
  /-- Map one complete proof-relevant region tree.  Static nodes retain their
  mapped plan and mapped occurrence forest; neutral frames are transported
  structurally. -/
  def mapCostRegionTree {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern}
      {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      CostRegionTree target
        (targetFree.map morphism.costWholeStructural.symbols)
        (available.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (outer.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (mapPattern morphism.costWholeStructural.symbols pattern)
        (mapTypeExpr morphism.costWholeStructural.symbols type) :=
    match tree with
    | @CostRegionTree.bvar _ _ available outer index type lookup => by
        exact .bvar (by
          rw [← List.map_append, List.getElem?_map, lookup]
          rfl)
    | .fvar lookup =>
        .fvar (by
          unfold WellSorted.FreeTypeContext.map
          rw [lookup]
          rfl)
    | @CostRegionTree.static _ _ color outer node children => by
        let mappedNode := node.map morphism scope laws
        let mappedChildren := mapCostRegionBoundaryTrees morphism scope laws
          children
        let alignedChildren := CostRegionBoundaryTrees.reindexPacket
          (node.map_boundaryPacket morphism scope laws).symm mappedChildren
        let mappedTree := CostRegionTree.static (outer :=
          outer.map (mapTypeExpr morphism.costWholeStructural.symbols))
          mappedNode alignedChildren
        have typeEquality :
            (.base
              (color.mapLangSort target mappedNode.sourceSort).1 : TypeExpr) =
              mapTypeExpr morphism.costWholeStructural.symbols
                (.base (color.mapLangSort source node.sourceSort).1) := by
          rw [CostStaticRegionNode.map_sourceSort]
          exact (morphism.mapTypeExpr_costStatic_natural color
            (.base node.sourceSort.1)).symm
        exact CostRegionTree.reindex
          (node.map_targetBound morphism scope laws) rfl
          (node.map_term_pattern morphism scope laws) typeEquality mappedTree
    | @CostRegionTree.neutralApplicationOrdinary _ _ available outer rule
        arguments membership notBare constructor materializes neutral ordinary
        children => by
        have mappedNotBare :
            ¬ WellSorted.UsesBareCollection
              (mapGrammarRule morphism.costWholeStructural.symbols rule) := by
          intro bare
          exact notBare
            ((WellSorted.usesBareCollection_mapGrammarRule_iff
              morphism.costWholeStructural.symbols rule).mp bare)
        have mappedNeutral :
            target.declaredCostConstructorRole
                (morphism.mapDeclaredCostConstructor constructor) =
                  .interactionPrincipal ∨
              ∃ kind, target.declaredCostConstructorRole
                (morphism.mapDeclaredCostConstructor constructor) =
                  .apparatus kind := by
          rcases neutral with principal | ⟨kind, apparatus⟩
          · exact Or.inl
              ((morphism.declaredCostConstructorRole_map constructor).trans
                principal)
          · exact Or.inr ⟨kind,
              (morphism.declaredCostConstructorRole_map constructor).trans
                apparatus⟩
        have mappedOrdinary :
            ReflectiveContextSupport.isQuoteConstructor
                target.costWholeReflectionProfile
                (mapGrammarRule
                  morphism.costWholeStructural.symbols rule).label = false :=
          (laws.quoteClassificationNatural rule.label).trans ordinary
        let mappedChildren := mapCostRegionArgumentTrees morphism scope laws
          children
        let mappedTree := CostRegionTree.neutralApplicationOrdinary
          (morphism.costWholeStructural.mapsTerms rule membership)
          mappedNotBare (morphism.mapDeclaredCostConstructor constructor)
          ((morphism.materialize_mapDeclaredCostConstructor constructor).trans
            (congrArg
              (mapGrammarRule morphism.costWholeStructural.symbols)
              materializes))
          mappedNeutral mappedOrdinary mappedChildren
        have patternEquality :
            (.apply
              (mapGrammarRule morphism.costWholeStructural.symbols rule).label
              (arguments.map
                (mapPattern morphism.costWholeStructural.symbols))) =
              mapPattern morphism.costWholeStructural.symbols
                (.apply rule.label arguments) := by
          simp [mapPattern, mapPatternList_eq_map, mapGrammarRule]
        have typeEquality :
            (.base
              (mapGrammarRule
                morphism.costWholeStructural.symbols rule).category :
                TypeExpr) =
              mapTypeExpr morphism.costWholeStructural.symbols
                (.base rule.category) := by
          rfl
        exact CostRegionTree.reindex rfl rfl patternEquality typeEquality
          mappedTree
    | @CostRegionTree.neutralApplicationQuote _ _ available outer rule
        arguments membership notBare constructor materializes neutral quoted
        children => by
        have mappedNotBare :
            ¬ WellSorted.UsesBareCollection
              (mapGrammarRule morphism.costWholeStructural.symbols rule) := by
          intro bare
          exact notBare
            ((WellSorted.usesBareCollection_mapGrammarRule_iff
              morphism.costWholeStructural.symbols rule).mp bare)
        have mappedNeutral :
            target.declaredCostConstructorRole
                (morphism.mapDeclaredCostConstructor constructor) =
                  .interactionPrincipal ∨
              ∃ kind, target.declaredCostConstructorRole
                (morphism.mapDeclaredCostConstructor constructor) =
                  .apparatus kind := by
          rcases neutral with principal | ⟨kind, apparatus⟩
          · exact Or.inl
              ((morphism.declaredCostConstructorRole_map constructor).trans
                principal)
          · exact Or.inr ⟨kind,
              (morphism.declaredCostConstructorRole_map constructor).trans
                apparatus⟩
        have mappedQuoted :
            ReflectiveContextSupport.isQuoteConstructor
                target.costWholeReflectionProfile
                (mapGrammarRule
                  morphism.costWholeStructural.symbols rule).label = true :=
          (laws.quoteClassificationNatural rule.label).trans quoted
        let mappedChildren := mapCostRegionArgumentTrees morphism scope laws
          children
        have outerEquality :
            (available ++ outer).map
                (mapTypeExpr morphism.costWholeStructural.symbols) =
              available.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) ++
                outer.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) := by
          rw [List.map_append]
        let alignedChildren := CostRegionArgumentTrees.reindexOuter
          outerEquality mappedChildren
        let mappedTree := CostRegionTree.neutralApplicationQuote
          (morphism.costWholeStructural.mapsTerms rule membership)
          mappedNotBare (morphism.mapDeclaredCostConstructor constructor)
          ((morphism.materialize_mapDeclaredCostConstructor constructor).trans
            (congrArg
              (mapGrammarRule morphism.costWholeStructural.symbols)
              materializes))
          mappedNeutral mappedQuoted alignedChildren
        have patternEquality :
            (.apply
              (mapGrammarRule morphism.costWholeStructural.symbols rule).label
              (arguments.map
                (mapPattern morphism.costWholeStructural.symbols))) =
              mapPattern morphism.costWholeStructural.symbols
                (.apply rule.label arguments) := by
          simp [mapPattern, mapPatternList_eq_map, mapGrammarRule]
        have typeEquality :
            (.base
              (mapGrammarRule
                morphism.costWholeStructural.symbols rule).category :
                TypeExpr) =
              mapTypeExpr morphism.costWholeStructural.symbols
                (.base rule.category) := by
          rfl
        exact CostRegionTree.reindex rfl rfl patternEquality typeEquality
          mappedTree
    | @CostRegionTree.lambda _ _ available outer binder body domain codomain
        bodyTree =>
        .lambda (mapCostRegionTree morphism scope laws bodyTree)
    | @CostRegionTree.multiLambda _ _ available outer arity binders body domain
        codomain bodyTree => by
        have mappedBody := mapCostRegionTree morphism scope laws bodyTree
        have availableEquality :
            (List.replicate arity domain ++ available).map
                (mapTypeExpr morphism.costWholeStructural.symbols) =
              List.replicate arity
                  (mapTypeExpr morphism.costWholeStructural.symbols domain) ++
                available.map
                  (mapTypeExpr morphism.costWholeStructural.symbols) := by
          simp [List.map_append]
        let alignedBody := mappedBody.reindexAvailable availableEquality
        exact CostRegionTree.multiLambda alignedBody
    | @CostRegionTree.subst _ _ available outer body replacement domain
        codomain bodyTree replacementTree =>
        .subst (mapCostRegionTree morphism scope laws bodyTree)
          (mapCostRegionTree morphism scope laws replacementTree)
    | @CostRegionTree.collection _ _ available outer collectionType elements
        rest elementType children => by
        let mappedChildren := mapCostRegionElementTrees morphism scope laws
          children
        let mappedTree := CostRegionTree.collection
          (collectionType := collectionType) (rest := rest) mappedChildren
        have patternEquality :
            (.collection collectionType
              (elements.map
                (mapPattern morphism.costWholeStructural.symbols)) rest) =
              mapPattern morphism.costWholeStructural.symbols
                (.collection collectionType elements rest) := by
          simp [mapPattern, mapPatternList_eq_map]
        have typeEquality :
            (.collection collectionType
              (mapTypeExpr morphism.costWholeStructural.symbols elementType) :
                TypeExpr) =
              mapTypeExpr morphism.costWholeStructural.symbols
                (.collection collectionType elementType) := by
          rfl
        exact CostRegionTree.reindex rfl rfl patternEquality typeEquality
          mappedTree

  /-- Map an ordered constructor-argument forest. -/
  def mapCostRegionArgumentTrees {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      CostRegionArgumentTrees target
        (targetFree.map morphism.costWholeStructural.symbols)
        (available.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (outer.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (arguments.map (mapPattern morphism.costWholeStructural.symbols))
        (parameters.map
          (mapTermParam morphism.costWholeStructural.symbols)) :=
    match trees with
    | .nil => .nil
    | @CostRegionArgumentTrees.cons _ _ _ _ argument arguments parameter
        parameters expected representation parameterType head tail =>
        .cons
          ((WellSorted.matchesParameterRepresentation_map_iff
            morphism.costWholeStructural.symbols parameter argument).2
              representation)
          (by
            rw [WellSorted.parameterType?_mapTermParam, parameterType]
            rfl)
          (mapCostRegionTree morphism scope laws head)
          (mapCostRegionArgumentTrees morphism scope laws tail)

  /-- Map a homogeneous collection-element forest. -/
  def mapCostRegionElementTrees {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer
        elements elementType) :
      CostRegionElementTrees target
        (targetFree.map morphism.costWholeStructural.symbols)
        (available.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (outer.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (elements.map (mapPattern morphism.costWholeStructural.symbols))
        (mapTypeExpr morphism.costWholeStructural.symbols elementType) :=
    match trees with
    | .nil _ _ _ => .nil _ _ _
    | .cons head tail =>
        .cons (mapCostRegionTree morphism scope laws head)
          (mapCostRegionElementTrees morphism scope laws tail)

  /-- Map a recursive forest aligned with an exact finite boundary table. -/
  def mapCostRegionBoundaryTrees {source target : CIGSLT}
      (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      CostRegionBoundaryTrees target
        (targetFree.map morphism.costWholeStructural.symbols) color
        (TypedCostRegionBoundaryTable.map morphism scope color table) :=
    match trees with
    | .nil => .nil
    | @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences boundary
        content tail head children =>
        .cons (mapCostRegionTree morphism scope laws head)
          (mapCostRegionBoundaryTrees morphism scope laws children)
end

namespace CostElaborationIndex

/-- Transport the complete typed index of one proof-relevant Cost fibre. -/
def map {source target : CIGSLT}
    (morphism : source.Morphism target)
    (index : CostElaborationIndex source) :
    CostElaborationIndex target where
  targetFree := index.targetFree.map morphism.costWholeStructural.symbols
  targetBound := index.targetBound.map
    (mapTypeExpr morphism.costWholeStructural.symbols)
  targetSort := WellSorted.mapLangSort morphism.costWholeStructural
    index.targetSort

end CostElaborationIndex

/-- Transport one exact open elaboration without rerunning the region
compiler.  The mapped tree retains the source decomposition choices and
ordered boundary occurrences. -/
def CostOpenElaboration.map {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    CostOpenElaboration target (morphism.mapCostOpenTerm scope term) where
  tree := mapCostRegionTree morphism scope laws elaboration.tree

/-- Transport one intrinsically typed proof-relevant Cost term. -/
def CostElabTerm.map {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    CostElabTerm target
      (targetFree.map morphism.costWholeStructural.symbols)
      (targetBound.map (mapTypeExpr morphism.costWholeStructural.symbols))
      (WellSorted.mapLangSort morphism.costWholeStructural targetSort) :=
  ⟨morphism.mapCostOpenTerm scope term.1, term.2.map morphism scope laws⟩

/-- Transport an arbitrary member of the sigma-bundled elaboration fibre. -/
def mapCostElaborationFiber {source target : CIGSLT}
    (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    (fiber : CostElaborationFiber source) : CostElaborationFiber target :=
  ⟨fiber.1.map morphism, fiber.2.map morphism scope laws⟩

end Mettapedia.GSLT.LanguageDef
