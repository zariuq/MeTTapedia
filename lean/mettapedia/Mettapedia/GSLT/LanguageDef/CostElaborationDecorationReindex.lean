import Mettapedia.GSLT.LanguageDef.CostElaborationConservative
import Mettapedia.GSLT.LanguageDef.CostElaborationDecoration

/-!
# Functorial reindexing of complete Cost decorations

The checked region tree is dependently indexed by its typing fibre.  Its
`CostTreeDecoration` projection retains every computational choice while
discarding only proof terms.  This module maps that nondependent projection
strictly along continued morphisms and proves identity and composition.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

mutual
  /-- Map the complete computational snapshot of one static plan. -/
  def CostStaticPlanDecoration.map {source target : CIGSLT}
      (morphism : source.Morphism target) :
      CostStaticPlanDecoration source → CostStaticPlanDecoration target
    | .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node =>
      .mk
        (sourceBound.map
          (mapTypeExpr
            morphism.underlying.structural.structural.symbols))
        (targetBound.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (sourceAvailable.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols outer)
        (mapPattern morphism.costWholeStructural.symbols pattern)
        (mapTypeExpr
          morphism.underlying.structural.structural.symbols sourceType)
        (boundaries.map (CostRegionBoundary.map morphism))
        (node.map morphism)
  termination_by decoration => sizeOf decoration

  /-- Map the proof-relevant choice at one static-plan node. -/
  def CostStaticPlanDecorationNode.map {source target : CIGSLT}
      (morphism : source.Morphism target) :
      CostStaticPlanDecorationNode source →
        CostStaticPlanDecorationNode target
    | .bvar sourceIndex => .bvar sourceIndex
    | .fvar sourceName => .fvar sourceName
    | .boundaryApplication constructor boundary =>
        .boundaryApplication
          (morphism.mapDeclaredCostConstructor constructor)
          (boundary.map morphism)
    | .application sourceLabel constructor children =>
        .application
          (morphism.underlying.structural.structural.symbols.constructor
            sourceLabel)
          (morphism.mapDeclaredCostConstructor constructor)
          (mapCostStaticPlanDecorations morphism children)
    | .lambda binder body => .lambda binder (body.map morphism)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (body.map morphism)
    | .collection collectionType sourceRest choice children =>
        .collection collectionType sourceRest
          (choice.map
            morphism.underlying.structural.structural.symbols)
          (mapCostStaticPlanDecorations morphism children)
    | .boundaryCollection collectionType oppositeChoice boundary =>
        .boundaryCollection collectionType
          (oppositeChoice.map
            morphism.underlying.structural.structural.symbols)
          (boundary.map morphism)
  termination_by node => sizeOf node

  /-- Map an ordered list of static-plan decorations. -/
  def mapCostStaticPlanDecorations {source target : CIGSLT}
      (morphism : source.Morphism target) :
      List (CostStaticPlanDecoration source) →
        List (CostStaticPlanDecoration target)
    | [] => []
    | decoration :: decorations =>
        decoration.map morphism ::
          mapCostStaticPlanDecorations morphism decorations
  termination_by decorations => sizeOf decorations
  decreasing_by all_goals simp_all <;> omega
end

mutual
  /-- Map the complete nondependent snapshot of one checked Cost region
  tree. -/
  def CostTreeDecoration.map {source target : CIGSLT}
      (morphism : source.Morphism target) :
      CostTreeDecoration source → CostTreeDecoration target
    | .mk available outer pattern type node =>
      .mk
        (available.map
          (mapTypeExpr morphism.costWholeStructural.symbols))
        (outer.map (mapTypeExpr morphism.costWholeStructural.symbols))
        (mapPattern morphism.costWholeStructural.symbols pattern)
        (mapTypeExpr morphism.costWholeStructural.symbols type)
        (node.map morphism)
  termination_by decoration => sizeOf decoration

  /-- Map one complete tree-decoration node.  Lists are mapped in their
  authored order, so equal boundary contents remain separate occurrences. -/
  def CostTreeDecorationNode.map {source target : CIGSLT}
      (morphism : source.Morphism target) :
      CostTreeDecorationNode source → CostTreeDecorationNode target
    | .bvar => .bvar
    | .fvar => .fvar
    | .static color sourceSort plan boundaries =>
        .static color
          (morphism.underlying.structural.structural.symbols.sort sourceSort)
          (plan.map morphism)
          (mapCostBoundaryDecorations morphism boundaries)
    | .neutralApplication kind constructor arguments =>
        .neutralApplication kind
          (morphism.mapDeclaredCostConstructor constructor)
          (mapCostTreeDecorations morphism arguments)
    | .lambda body => .lambda (body.map morphism)
    | .multiLambda body => .multiLambda (body.map morphism)
    | .subst body replacement =>
        .subst (body.map morphism) (replacement.map morphism)
    | .collection elements =>
        .collection (mapCostTreeDecorations morphism elements)
  termination_by node => sizeOf node

  /-- Map an ordered list of complete tree decorations. -/
  def mapCostTreeDecorations {source target : CIGSLT}
      (morphism : source.Morphism target) :
      List (CostTreeDecoration source) → List (CostTreeDecoration target)
    | [] => []
    | decoration :: decorations =>
        decoration.map morphism :: mapCostTreeDecorations morphism decorations
  termination_by decorations => sizeOf decorations

  /-- Map an ordered boundary/decorated-child list without identifying
  repeated boundary records. -/
  def mapCostBoundaryDecorations {source target : CIGSLT}
      (morphism : source.Morphism target) :
      List (CostRegionBoundary × CostTreeDecoration source) →
        List (CostRegionBoundary × CostTreeDecoration target)
    | [] => []
    | (boundary, decoration) :: boundaries =>
        (boundary.map morphism, decoration.map morphism) ::
          mapCostBoundaryDecorations morphism boundaries
  termination_by boundaries => sizeOf boundaries
  decreasing_by all_goals simp_all <;> omega
end

@[simp]
theorem CIGSLT.Morphism.sourceSymbols_id (source : CIGSLT) :
    (CIGSLT.Morphism.id source).underlying.structural.structural.symbols =
      LanguageDefSymbolMap.id :=
  rfl

@[simp]
theorem CIGSLT.Morphism.costWholeSymbols_id (source : CIGSLT) :
    (CIGSLT.Morphism.id source).costWholeStructural.symbols =
      LanguageDefSymbolMap.id := by
  change costLanguageDefSymbolMap LanguageDefSymbolMap.id = _
  exact costLanguageDefSymbolMap_id

@[simp]
private theorem mapTypeExprList_id (types : List TypeExpr) :
    types.map (mapTypeExpr LanguageDefSymbolMap.id) = types := by
  induction types <;> simp_all

@[simp]
private theorem mapCostRegionBoundaries_id (source : CIGSLT)
    (boundaries : List CostRegionBoundary) :
    boundaries.map (CostRegionBoundary.map (CIGSLT.Morphism.id source)) =
      boundaries := by
  induction boundaries <;> simp_all

mutual
  /-- Static-plan decorations are unchanged by identity reindexing. -/
  @[simp]
  theorem CostStaticPlanDecoration.map_id (source : CIGSLT)
      (decoration : CostStaticPlanDecoration source) :
      decoration.map (CIGSLT.Morphism.id source) = decoration :=
    match decoration with
    | .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node => by
      simp only [CostStaticPlanDecoration.map,
        CIGSLT.Morphism.sourceSymbols_id,
        CIGSLT.Morphism.costWholeSymbols_id, mapTypeExpr_id,
        CIGSLT.mapOneHoleContext_id, mapPattern_id,
        mapTypeExprList_id, mapCostRegionBoundaries_id,
        CostStaticPlanDecorationNode.map_id]

  /-- Static-plan choices are unchanged by identity reindexing. -/
  @[simp]
  theorem CostStaticPlanDecorationNode.map_id (source : CIGSLT)
      (node : CostStaticPlanDecorationNode source) :
      node.map (CIGSLT.Morphism.id source) = node :=
    match node with
    | .bvar sourceIndex => by
      simp only [CostStaticPlanDecorationNode.map]
    | .fvar sourceName => by
      simp only [CostStaticPlanDecorationNode.map]
    | .boundaryApplication constructor boundary => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.mapDeclaredCostConstructor_id,
        CostRegionBoundary.map_id]
    | .application sourceLabel constructor children => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_id, LanguageDefSymbolMap.id,
        id_eq,
        CIGSLT.Morphism.mapDeclaredCostConstructor_id,
        mapCostStaticPlanDecorations_id]
    | .lambda binder body => by
      simp only [CostStaticPlanDecorationNode.map,
        CostStaticPlanDecoration.map_id]
    | .multiLambda arity binders body => by
      simp only [CostStaticPlanDecorationNode.map,
        CostStaticPlanDecoration.map_id]
    | .collection collectionType sourceRest choice children => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_id,
        CostCollectionTypingChoice.map_id,
        mapCostStaticPlanDecorations_id]
    | .boundaryCollection collectionType oppositeChoice boundary => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_id,
        CostCollectionTypingChoice.map_id, CostRegionBoundary.map_id]

  /-- Ordered static-plan decoration lists are unchanged by identity
  reindexing. -/
  @[simp]
  theorem mapCostStaticPlanDecorations_id (source : CIGSLT)
      (decorations : List (CostStaticPlanDecoration source)) :
      mapCostStaticPlanDecorations (CIGSLT.Morphism.id source) decorations =
        decorations :=
    match decorations with
    | [] => by
      simp only [mapCostStaticPlanDecorations]
    | decoration :: decorations => by
      rw [mapCostStaticPlanDecorations]
      rw [CostStaticPlanDecoration.map_id,
        mapCostStaticPlanDecorations_id]
end

mutual
  /-- Complete tree decorations are unchanged by identity reindexing. -/
  @[simp]
  theorem CostTreeDecoration.map_id (source : CIGSLT)
      (decoration : CostTreeDecoration source) :
      decoration.map (CIGSLT.Morphism.id source) = decoration :=
    match decoration with
    | .mk available outer pattern type node => by
      simp only [CostTreeDecoration.map,
        CIGSLT.Morphism.costWholeSymbols_id, mapTypeExpr_id,
        mapPattern_id, mapTypeExprList_id, CostTreeDecorationNode.map_id]

  /-- Complete tree-decoration choices are unchanged by identity
  reindexing. -/
  @[simp]
  theorem CostTreeDecorationNode.map_id (source : CIGSLT)
      (node : CostTreeDecorationNode source) :
      node.map (CIGSLT.Morphism.id source) = node :=
    match node with
    | .bvar => by
      simp only [CostTreeDecorationNode.map]
    | .fvar => by
      simp only [CostTreeDecorationNode.map]
    | .static color sourceSort plan boundaries => by
      simp only [CostTreeDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_id, LanguageDefSymbolMap.id,
        id_eq,
        CostStaticPlanDecoration.map_id, mapCostBoundaryDecorations_id]
    | .neutralApplication kind constructor arguments => by
      simp only [CostTreeDecorationNode.map,
        CIGSLT.Morphism.mapDeclaredCostConstructor_id,
        mapCostTreeDecorations_id]
    | .lambda body => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_id]
    | .multiLambda body => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_id]
    | .subst body replacement => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_id]
    | .collection elements => by
      simp only [CostTreeDecorationNode.map, mapCostTreeDecorations_id]

  /-- Ordered tree-decoration lists are unchanged by identity reindexing. -/
  @[simp]
  theorem mapCostTreeDecorations_id (source : CIGSLT)
      (decorations : List (CostTreeDecoration source)) :
      mapCostTreeDecorations (CIGSLT.Morphism.id source) decorations =
        decorations :=
    match decorations with
    | [] => by
      simp only [mapCostTreeDecorations]
    | decoration :: decorations => by
      rw [mapCostTreeDecorations]
      rw [CostTreeDecoration.map_id, mapCostTreeDecorations_id]

  /-- Ordered boundary/decorated-child lists are unchanged by identity
  reindexing. -/
  @[simp]
  theorem mapCostBoundaryDecorations_id (source : CIGSLT)
      (boundaries : List (CostRegionBoundary × CostTreeDecoration source)) :
      mapCostBoundaryDecorations (CIGSLT.Morphism.id source) boundaries =
        boundaries :=
    match boundaries with
    | [] => by
      simp only [mapCostBoundaryDecorations]
    | (boundary, decoration) :: boundaries => by
      rw [mapCostBoundaryDecorations]
      rw [CostRegionBoundary.map_id, CostTreeDecoration.map_id,
        mapCostBoundaryDecorations_id]
end

@[simp]
theorem CIGSLT.Morphism.sourceSymbols_comp
    {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third) :
    (CIGSLT.Morphism.comp left right).underlying.structural.structural.symbols =
      left.underlying.structural.structural.symbols.comp
        right.underlying.structural.structural.symbols :=
  rfl

@[simp]
theorem CIGSLT.Morphism.costWholeSymbols_comp
    {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third) :
    (CIGSLT.Morphism.comp left right).costWholeStructural.symbols =
      left.costWholeStructural.symbols.comp
        right.costWholeStructural.symbols := by
  exact costLanguageDefSymbolMap_comp
    left.underlying.structural.structural.symbols
    right.underlying.structural.structural.symbols

private theorem mapTypeExprList_comp
    (first second : LanguageDefSymbolMap) (types : List TypeExpr) :
    types.map (mapTypeExpr (first.comp second)) =
      (types.map (mapTypeExpr first)).map (mapTypeExpr second) := by
  rw [List.map_map]
  exact List.map_congr_left fun type _ => mapTypeExpr_comp first second type

private theorem mapCostRegionBoundaries_comp
    {first second third : CIGSLT}
    (left : first.Morphism second) (right : second.Morphism third)
    (boundaries : List CostRegionBoundary) :
    boundaries.map
        (CostRegionBoundary.map (CIGSLT.Morphism.comp left right)) =
      (boundaries.map (CostRegionBoundary.map left)).map
        (CostRegionBoundary.map right) := by
  rw [List.map_map]
  exact List.map_congr_left fun boundary _ =>
    CostRegionBoundary.map_comp left right boundary

mutual
  /-- Static-plan decoration transport is strictly compositional. -/
  theorem CostStaticPlanDecoration.map_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (decoration : CostStaticPlanDecoration first) :
      decoration.map (CIGSLT.Morphism.comp left right) =
        (decoration.map left).map right :=
    match decoration with
    | .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node => by
      simp only [CostStaticPlanDecoration.map,
        CIGSLT.Morphism.sourceSymbols_comp,
        CIGSLT.Morphism.costWholeSymbols_comp,
        mapTypeExprList_comp, CIGSLT.mapOneHoleContext_comp,
        mapPattern_comp, mapTypeExpr_comp,
        mapCostRegionBoundaries_comp,
        CostStaticPlanDecorationNode.map_comp]

  /-- Static-plan node choices transport strictly through a composite. -/
  theorem CostStaticPlanDecorationNode.map_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (node : CostStaticPlanDecorationNode first) :
      node.map (CIGSLT.Morphism.comp left right) =
        (node.map left).map right :=
    match node with
    | .bvar sourceIndex => by
      simp only [CostStaticPlanDecorationNode.map]
    | .fvar sourceName => by
      simp only [CostStaticPlanDecorationNode.map]
    | .boundaryApplication constructor boundary => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.mapDeclaredCostConstructor_comp,
        CostRegionBoundary.map_comp]
    | .application sourceLabel constructor children => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_comp, LanguageDefSymbolMap.comp,
        Function.comp_apply,
        CIGSLT.Morphism.mapDeclaredCostConstructor_comp,
        mapCostStaticPlanDecorations_comp]
    | .lambda binder body => by
      simp only [CostStaticPlanDecorationNode.map,
        CostStaticPlanDecoration.map_comp]
    | .multiLambda arity binders body => by
      simp only [CostStaticPlanDecorationNode.map,
        CostStaticPlanDecoration.map_comp]
    | .collection collectionType sourceRest choice children => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_comp,
        CostCollectionTypingChoice.map_comp,
        mapCostStaticPlanDecorations_comp]
    | .boundaryCollection collectionType oppositeChoice boundary => by
      simp only [CostStaticPlanDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_comp,
        CostCollectionTypingChoice.map_comp, CostRegionBoundary.map_comp]

  /-- Ordered static-plan decoration lists transport strictly through a
  composite. -/
  theorem mapCostStaticPlanDecorations_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (decorations : List (CostStaticPlanDecoration first)) :
      mapCostStaticPlanDecorations (CIGSLT.Morphism.comp left right)
          decorations =
        mapCostStaticPlanDecorations right
          (mapCostStaticPlanDecorations left decorations) :=
    match decorations with
    | [] => by
      simp only [mapCostStaticPlanDecorations]
    | decoration :: decorations => by
      rw [mapCostStaticPlanDecorations]
      rw [mapCostStaticPlanDecorations]
      rw [mapCostStaticPlanDecorations]
      rw [CostStaticPlanDecoration.map_comp,
        mapCostStaticPlanDecorations_comp]
end

mutual
  /-- Complete tree-decoration transport is strictly compositional. -/
  theorem CostTreeDecoration.map_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (decoration : CostTreeDecoration first) :
      decoration.map (CIGSLT.Morphism.comp left right) =
        (decoration.map left).map right :=
    match decoration with
    | .mk available outer pattern type node => by
      simp only [CostTreeDecoration.map,
        CIGSLT.Morphism.costWholeSymbols_comp,
        mapTypeExprList_comp, mapPattern_comp, mapTypeExpr_comp,
        CostTreeDecorationNode.map_comp]

  /-- Complete tree node choices transport strictly through a composite. -/
  theorem CostTreeDecorationNode.map_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (node : CostTreeDecorationNode first) :
      node.map (CIGSLT.Morphism.comp left right) =
        (node.map left).map right :=
    match node with
    | .bvar => by
      simp only [CostTreeDecorationNode.map]
    | .fvar => by
      simp only [CostTreeDecorationNode.map]
    | .static color sourceSort plan boundaries => by
      simp only [CostTreeDecorationNode.map,
        CIGSLT.Morphism.sourceSymbols_comp, LanguageDefSymbolMap.comp,
        Function.comp_apply, CostStaticPlanDecoration.map_comp,
        mapCostBoundaryDecorations_comp]
    | .neutralApplication kind constructor arguments => by
      simp only [CostTreeDecorationNode.map,
        CIGSLT.Morphism.mapDeclaredCostConstructor_comp,
        mapCostTreeDecorations_comp]
    | .lambda body => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_comp]
    | .multiLambda body => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_comp]
    | .subst body replacement => by
      simp only [CostTreeDecorationNode.map, CostTreeDecoration.map_comp]
    | .collection elements => by
      simp only [CostTreeDecorationNode.map, mapCostTreeDecorations_comp]

  /-- Ordered tree-decoration lists transport strictly through a
  composite. -/
  theorem mapCostTreeDecorations_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (decorations : List (CostTreeDecoration first)) :
      mapCostTreeDecorations (CIGSLT.Morphism.comp left right) decorations =
        mapCostTreeDecorations right
          (mapCostTreeDecorations left decorations) :=
    match decorations with
    | [] => by
      simp only [mapCostTreeDecorations]
    | decoration :: decorations => by
      rw [mapCostTreeDecorations]
      rw [mapCostTreeDecorations]
      rw [mapCostTreeDecorations]
      rw [CostTreeDecoration.map_comp, mapCostTreeDecorations_comp]

  /-- Ordered boundary/decorated-child lists transport strictly through a
  composite, without quotienting duplicate occurrences. -/
  theorem mapCostBoundaryDecorations_comp
      {first second third : CIGSLT}
      (left : first.Morphism second) (right : second.Morphism third)
      (boundaries : List (CostRegionBoundary × CostTreeDecoration first)) :
      mapCostBoundaryDecorations (CIGSLT.Morphism.comp left right)
          boundaries =
        mapCostBoundaryDecorations right
          (mapCostBoundaryDecorations left boundaries) :=
    match boundaries with
    | [] => by
      simp only [mapCostBoundaryDecorations]
    | (boundary, decoration) :: boundaries => by
      rw [mapCostBoundaryDecorations]
      rw [mapCostBoundaryDecorations]
      rw [mapCostBoundaryDecorations]
      rw [CostRegionBoundary.map_comp, CostTreeDecoration.map_comp,
        mapCostBoundaryDecorations_comp]
end

end Mettapedia.GSLT.LanguageDef
