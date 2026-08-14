import Mettapedia.GSLT.LanguageDef.CostElaborationTreeReindex
import Mettapedia.GSLT.LanguageDef.CostElaborationDecorationReindex

/-!
# Naturality of proof-relevant Cost tree reindexing

The dependent reindexing operation on checked Cost region trees and the
strict map on their nondependent decorations are defined independently.
This module relates them.  The comparison retains every plan choice and
ordered boundary occurrence; only proof terms and dependent equality casts
are ignored by the decoration.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- Mapping a typed boundary table maps its retained entries pointwise and
keeps their authored order. -/
@[simp]
theorem TypedCostRegionBoundaryTable.entries_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (color : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree
      occurrences) :
    (TypedCostRegionBoundaryTable.map morphism scope color table).entries =
      table.entries.map fun boundary => boundary.map morphism scope := by
  induction table with
  | nil => rfl
  | cons boundary content tail inductionHypothesis =>
      change boundary.map morphism scope ::
          (TypedCostRegionBoundaryTable.map morphism scope color tail).entries =
        boundary.map morphism scope ::
          (tail.entries.map fun entry => entry.map morphism scope)
      rw [inductionHypothesis]

/-- The empty boundary table displays no occurrence. -/
@[simp]
theorem TypedCostRegionBoundaryTable.entries_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} :
    (TypedCostRegionBoundaryTable.nil (source := source) (color := color)
      (targetFree := targetFree)).entries = [] :=
  rfl

/-- Mapping a plan decoration maps its displayed boundary occurrences
pointwise. -/
@[simp]
theorem CostStaticPlanDecoration.boundaries_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).boundaries =
      decoration.boundaries.map (CostRegionBoundary.map morphism) := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its source binder context pointwise. -/
@[simp]
theorem CostStaticPlanDecoration.sourceBound_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).sourceBound =
      decoration.sourceBound.map
        (mapTypeExpr morphism.underlying.structural.structural.symbols) := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its target binder context pointwise. -/
@[simp]
theorem CostStaticPlanDecoration.targetBound_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).targetBound =
      decoration.targetBound.map
        (mapTypeExpr morphism.costWholeStructural.symbols) := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its available source context pointwise. -/
@[simp]
theorem CostStaticPlanDecoration.sourceAvailable_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).sourceAvailable =
      decoration.sourceAvailable.map
        (mapTypeExpr morphism.costWholeStructural.symbols) := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its retained outer context. -/
@[simp]
theorem CostStaticPlanDecoration.outer_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).outer =
      CIGSLT.mapOneHoleContext morphism.costWholeStructural.symbols
        decoration.outer := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its compact pattern. -/
@[simp]
theorem CostStaticPlanDecoration.pattern_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).pattern =
      mapPattern morphism.costWholeStructural.symbols decoration.pattern := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its source type. -/
@[simp]
theorem CostStaticPlanDecoration.sourceType_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).sourceType =
      mapTypeExpr morphism.underlying.structural.structural.symbols
        decoration.sourceType := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a plan decoration maps its proof-relevant structural choice. -/
@[simp]
theorem CostStaticPlanDecoration.node_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostStaticPlanDecoration source) :
    (decoration.map morphism).node = decoration.node.map morphism := by
  cases decoration
  rw [CostStaticPlanDecoration.map.eq_1]
  rfl

/-- Mapping a tree decoration maps its active binder context pointwise. -/
@[simp]
theorem CostTreeDecoration.available_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostTreeDecoration source) :
    (decoration.map morphism).available =
      decoration.available.map
        (mapTypeExpr morphism.costWholeStructural.symbols) := by
  cases decoration
  rw [CostTreeDecoration.map.eq_1]
  rfl

/-- Mapping a tree decoration maps its sealed outer context pointwise. -/
@[simp]
theorem CostTreeDecoration.outer_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostTreeDecoration source) :
    (decoration.map morphism).outer =
      decoration.outer.map
        (mapTypeExpr morphism.costWholeStructural.symbols) := by
  cases decoration
  rw [CostTreeDecoration.map.eq_1]
  rfl

/-- Mapping a tree decoration maps its compact pattern. -/
@[simp]
theorem CostTreeDecoration.pattern_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostTreeDecoration source) :
    (decoration.map morphism).pattern =
      mapPattern morphism.costWholeStructural.symbols decoration.pattern := by
  cases decoration
  rw [CostTreeDecoration.map.eq_1]
  rfl

/-- Mapping a tree decoration maps its result type. -/
@[simp]
theorem CostTreeDecoration.type_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostTreeDecoration source) :
    (decoration.map morphism).type =
      mapTypeExpr morphism.costWholeStructural.symbols decoration.type := by
  cases decoration
  rw [CostTreeDecoration.map.eq_1]
  rfl

/-- Mapping a tree decoration maps its proof-relevant structural choice. -/
@[simp]
theorem CostTreeDecoration.node_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (decoration : CostTreeDecoration source) :
    (decoration.map morphism).node = decoration.node.map morphism := by
  cases decoration
  rw [CostTreeDecoration.map.eq_1]
  rfl

/-- Transporting the dependent indices of a region tree changes no retained
decoration data. -/
theorem CostRegionTree.decoration_reindex
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available₁ available₂ outer₁ outer₂ : List TypeExpr}
    {pattern₁ pattern₂ : Pattern} {type₁ type₂ : TypeExpr}
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (type : type₁ = type₂)
    (tree : CostRegionTree source targetFree available₁ outer₁ pattern₁
      type₁) :
    (tree.reindex available outer pattern type).decoration = tree.decoration := by
  subst available₂
  subst outer₂
  subst pattern₂
  subst type₂
  rfl

/-- Transporting a boundary forest along equality of its complete packet
changes no ordered boundary/child decoration. -/
theorem CostRegionBoundaryTrees.decorations_reindexPacket
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor}
    {sourcePacket targetPacket :
      TypedCostRegionBoundaryPacket source color targetFree}
    (packet : sourcePacket = targetPacket)
    (trees : CostRegionBoundaryTrees source targetFree color sourcePacket.2) :
    (trees.reindexPacket packet).decorations = trees.decorations := by
  subst targetPacket
  rfl

/-- Transporting only the sealed outer index of an argument forest changes
no ordered child decoration. -/
theorem CostRegionArgumentTrees.decorations_reindexOuter
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available first second : List TypeExpr} {arguments : List Pattern}
    {parameters : List TermParam}
    (outer : first = second)
    (trees : CostRegionArgumentTrees source targetFree available first
      arguments parameters) :
    (trees.reindexOuter outer).decorations = trees.decorations := by
  subst second
  rfl

/-- Transporting only the active binder index of a tree changes no retained
decoration. -/
theorem CostRegionTree.decoration_reindexAvailable
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {first second outer : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr}
    (available : first = second)
    (tree : CostRegionTree source targetFree first outer pattern type) :
    (tree.reindexAvailable available).decoration = tree.decoration := by
  subst second
  rfl

/-- Reindexing the dependent indices of a static plan does not change its
computational decoration. -/
theorem CostStaticRegionPlan.decoration_reindex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {pattern₁ pattern₂ : Pattern}
    {sourceType₁ sourceType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (pattern : pattern₁ = pattern₂)
    (sourceType : sourceType₁ = sourceType₂)
    (plan : CostStaticRegionPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ pattern₁
        sourceType₁) :
    (plan.reindex (thinning₂ := thinning₂) sourceBound targetBound
      available outer pattern sourceType).decoration = plan.decoration := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst pattern₂
  subst sourceType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  rfl

/-- The nondependent decoration projection exposes a lambda body without
unfolding the plan's dependent indices. -/
@[simp]
theorem CostStaticRegionPlan.decoration_node_lambda
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {binder : Option String} {body : Pattern}
    {domain codomain : TypeExpr}
    (bodyPlan : CostStaticRegionPlan source color targetFree
      (domain :: sourceBound)
      (mapTypeExpr (color.symbols source) domain :: targetBound)
      (CostStaticBinderThinning.mapped domain thinning)
      (mapTypeExpr (color.symbols source) domain :: sourceAvailable)
      (outer.comp (.lambda binder .hole)) body codomain) :
    (CostStaticRegionPlan.lambda bodyPlan).decoration.node =
      .lambda binder bodyPlan.decoration :=
  rfl

/-- The nondependent decoration projection exposes a multi-lambda body
without unfolding the plan's dependent indices. -/
@[simp]
theorem CostStaticRegionPlan.decoration_node_multiLambda
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {arity : Nat} {binders : List String}
    {body : Pattern} {domain codomain : TypeExpr}
    (bodyPlan : CostStaticRegionPlan source color targetFree
      (List.replicate arity domain ++ sourceBound)
      (List.replicate arity (mapTypeExpr (color.symbols source) domain) ++
        targetBound)
      (CostStaticBinderThinning.prependMapped arity domain thinning)
      (List.replicate arity (mapTypeExpr (color.symbols source) domain) ++
        sourceAvailable)
      (outer.comp (.multiLambda arity binders .hole)) body codomain) :
    (CostStaticRegionPlan.multiLambda bodyPlan).decoration.node =
      .multiLambda arity binders bodyPlan.decoration :=
  rfl

/-- Reindexing an argument plan changes no ordered plan decoration. -/
theorem CostStaticArgumentPlan.decorations_reindex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext} {wireName₁ wireName₂ : String}
    {before₁ before₂ arguments₁ arguments₂ : List Pattern}
    {parameters₁ parameters₂ : List TermParam}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂) (wireName : wireName₁ = wireName₂)
    (before : before₁ = before₂) (arguments : arguments₁ = arguments₂)
    (parameters : parameters₁ = parameters₂)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ wireName₁ before₁
        arguments₁ parameters₁) :
    (plan.reindex (thinning₂ := thinning₂) sourceBound targetBound
      available outer wireName before arguments parameters).decorations =
        plan.decorations := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst wireName₂
  subst before₂
  subst arguments₂
  subst parameters₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  rfl

/-- Reindexing a collection-element plan changes no ordered plan decoration. -/
theorem CostStaticElementPlan.decorations_reindex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound₁ sourceBound₂ targetBound₁ targetBound₂ : List TypeExpr}
    {thinning₁ : CostStaticBinderThinning source color sourceBound₁
      targetBound₁}
    {thinning₂ : CostStaticBinderThinning source color sourceBound₂
      targetBound₂}
    {available₁ available₂ : List TypeExpr}
    {outer₁ outer₂ : OneHoleContext}
    {collectionType₁ collectionType₂ : CollType}
    {before₁ before₂ elements₁ elements₂ : List Pattern}
    {rest₁ rest₂ : Option String}
    {sourceElementType₁ sourceElementType₂ : TypeExpr}
    (sourceBound : sourceBound₁ = sourceBound₂)
    (targetBound : targetBound₁ = targetBound₂)
    (available : available₁ = available₂)
    (outer : outer₁ = outer₂)
    (collectionType : collectionType₁ = collectionType₂)
    (before : before₁ = before₂) (elements : elements₁ = elements₂)
    (rest : rest₁ = rest₂)
    (sourceElementType : sourceElementType₁ = sourceElementType₂)
    (plan : CostStaticElementPlan source color targetFree sourceBound₁
      targetBound₁ thinning₁ available₁ outer₁ collectionType₁
        before₁ elements₁ rest₁ sourceElementType₁) :
    (plan.reindex (thinning₂ := thinning₂) sourceBound targetBound
      available outer collectionType before elements rest
        sourceElementType).decorations = plan.decorations := by
  subst sourceBound₂
  subst targetBound₂
  subst available₂
  subst outer₂
  subst collectionType₂
  subst before₂
  subst elements₂
  subst rest₂
  subst sourceElementType₂
  have thinning : thinning₁ = thinning₂ :=
    CostStaticBinderThinning.all_eq _ _
  subst thinning₂
  rfl

/-- Mapping a checked plan maps its retained boundary entries pointwise.  This
is extracted from the stronger dependent packet naturality theorem. -/
theorem mapCostStaticRegionPlan_boundaryEntries
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {targetAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning targetAvailable outer pattern sourceType)
    (object : WellSorted.isObjectPattern pattern = true) :
    (mapCostStaticRegionPlan morphism scope laws plan
        object).boundaryTable.entries.map (fun boundary => boundary.boundary) =
      (plan.boundaryTable.entries.map fun boundary => boundary.boundary).map
        (CostRegionBoundary.map morphism) := by
  have packet := mapCostStaticRegionPlan_boundaryPacket morphism scope laws
    plan object
  have displayed := congrArg
    (fun packet : TypedCostRegionBoundaryPacket target color
        (targetFree.map morphism.costWholeStructural.symbols) =>
      packet.2.entries.map fun boundary => boundary.boundary) packet
  have displayed' :
      (mapCostStaticRegionPlan morphism scope laws plan
          object).boundaryTable.entries.map
            (fun boundary => boundary.boundary) =
        (TypedCostRegionBoundaryTable.map morphism scope color
          plan.boundaryTable).entries.map
            (fun boundary => boundary.boundary) := by
    simpa only [TypedCostRegionBoundaryPacket.map,
      CostStaticRegionPlan.boundaryPacket] using displayed
  rw [TypedCostRegionBoundaryTable.entries_map] at displayed'
  simpa [List.map_map, Function.comp_def] using displayed'

/-- The boundary list displayed by a mapped plan is the pointwise map of the
source boundary list. -/
theorem mapCostStaticRegionPlan_boundaryDecorations
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {targetAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning targetAvailable outer pattern sourceType)
    (object : WellSorted.isObjectPattern pattern = true) :
    (mapCostStaticRegionPlan morphism scope laws plan
        object).decoration.boundaries =
      (plan.decoration.map morphism).boundaries := by
  simpa only [CostStaticRegionPlan.decoration_boundaries,
    CostStaticPlanDecoration.boundaries_map] using
      mapCostStaticRegionPlan_boundaryEntries morphism scope laws plan object

mutual
  /-- Mapping a checked static plan and then forgetting its proof fields is
  exactly the strict map of its complete plan decoration. -/
  theorem mapCostStaticRegionPlan_decoration
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {targetAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning targetAvailable outer pattern sourceType)
      (object : WellSorted.isObjectPattern pattern = true) :
      (mapCostStaticRegionPlan morphism scope laws plan object).decoration =
        plan.decoration.map morphism := by
    apply CostStaticPlanDecoration.ext
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact mapCostStaticRegionPlan_boundaryDecorations morphism scope laws
        plan object
    · rw [CostStaticPlanDecoration.node_map]
      cases plan with
      | bvar | fvar =>
          simp only [mapCostStaticRegionPlan,
            CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map]
      | boundaryApplication =>
          rw [mapCostStaticRegionPlan.eq_1]
          rw [CostStaticRegionPlan.decoration_reindex]
          simp [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map]
      | application constructor rendered current preimage notBare children =>
          have objects := WellSorted.objectArguments_of_objectApplication object
          have childEquality := mapCostStaticArgumentPlan_decorations morphism
            scope laws children objects
          rw [mapCostStaticRegionPlan.eq_1]
          rw [CostStaticRegionPlan.decoration_reindex]
          simp only [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map]
          congr 1
          apply Eq.trans ?_ childEquality
          apply CostStaticArgumentPlan.decorations_reindex
      | lambda bodyPlan =>
          have bodyObject := WellSorted.objectBody_of_objectLambda object
          have bodyEquality := mapCostStaticRegionPlan_decoration morphism scope
            laws bodyPlan bodyObject
          rw [mapCostStaticRegionPlan.eq_1]
          simpa [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map,
            CostStaticRegionPlan.decoration_reindex] using bodyEquality
      | multiLambda bodyPlan =>
          have bodyObject := WellSorted.objectBody_of_objectMultiLambda object
          have bodyEquality := mapCostStaticRegionPlan_decoration morphism scope
            laws bodyPlan bodyObject
          rw [mapCostStaticRegionPlan.eq_1]
          simpa [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map,
            CostStaticRegionPlan.decoration_reindex] using bodyEquality
      | collection choice selected children =>
          have objects := WellSorted.objectElements_of_objectCollection object
          have childEquality := mapCostStaticElementPlan_decorations morphism
            scope laws children objects
          rw [mapCostStaticRegionPlan.eq_1]
          rw [CostStaticRegionPlan.decoration_reindex]
          simp only [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map]
          congr 1
          apply Eq.trans ?_ childEquality
          apply CostStaticElementPlan.decorations_reindex
      | boundaryCollection =>
          rw [mapCostStaticRegionPlan.eq_1]
          rw [CostStaticRegionPlan.decoration_reindex]
          simp [CostStaticRegionPlan.decoration,
            CostStaticPlanDecoration.node,
            CostStaticPlanDecorationNode.map]
  termination_by 3 * sizeOf pattern + 2
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Mapping a static application spine maps its ordered plan decorations
  pointwise. -/
  theorem mapCostStaticArgumentPlan_decorations
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (objects : WellSorted.isObjectPatternList arguments = true) :
      (mapCostStaticArgumentPlan morphism scope laws plan objects).decorations =
        mapCostStaticPlanDecorations morphism plan.decorations := by
    cases plan with
    | nil =>
        rw [mapCostStaticArgumentPlan.eq_1]
        simp [CostStaticArgumentPlan.decorations,
          mapCostStaticPlanDecorations]
    | cons representation parameterType head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headEquality := mapCostStaticRegionPlan_decoration morphism scope
          laws head objectParts.1
        have tailEquality := mapCostStaticArgumentPlan_decorations morphism
          scope laws tail objectParts.2
        rw [mapCostStaticArgumentPlan.eq_1]
        simp only [CostStaticArgumentPlan.decorations,
          CostStaticRegionPlan.decoration_reindex,
          CostStaticArgumentPlan.decorations_reindex,
          mapCostStaticPlanDecorations]
        exact congrArg₂ List.cons headEquality tailEquality
  termination_by 3 * sizeOf arguments + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega

  /-- Mapping a static collection spine maps its ordered plan decorations
  pointwise. -/
  theorem mapCostStaticElementPlan_decorations
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound
        targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
          elements rest sourceElementType)
      (objects : WellSorted.isObjectPatternList elements = true) :
      (mapCostStaticElementPlan morphism scope laws plan objects).decorations =
        mapCostStaticPlanDecorations morphism plan.decorations := by
    cases plan with
    | nil =>
        rw [mapCostStaticElementPlan.eq_1]
        simp [CostStaticElementPlan.decorations,
          mapCostStaticPlanDecorations]
    | cons head tail =>
        have objectParts := WellSorted.objectList_cons objects
        have headEquality := mapCostStaticRegionPlan_decoration morphism scope
          laws head objectParts.1
        have tailEquality := mapCostStaticElementPlan_decorations morphism
          scope laws tail objectParts.2
        rw [mapCostStaticElementPlan.eq_1]
        simp only [CostStaticElementPlan.decorations,
          CostStaticRegionPlan.decoration_reindex,
          CostStaticElementPlan.decorations_reindex,
          mapCostStaticPlanDecorations]
        exact congrArg₂ List.cons headEquality tailEquality
  termination_by 3 * sizeOf elements + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- Mapping a static node maps the complete decoration of its sole retained
plan. -/
theorem CostStaticRegionNode.map_plan_decoration
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree) :
    (node.map morphism scope laws).plan.decoration =
      node.plan.decoration.map morphism := by
  rw [CostStaticRegionNode.map, CostStaticRegionNode.ofPlan_plan]
  change (node.mappedPlan morphism scope laws).decoration = _
  simpa [CostStaticRegionNode.mappedPlan,
    CostStaticRegionPlan.decoration_reindex] using
      mapCostStaticRegionPlan_decoration morphism scope laws node.plan
        node.term.2.2.2.1

private theorem mapCostRegionTree_decoration_of_node
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type)
    (nodeEquality :
      (mapCostRegionTree morphism scope laws tree).decoration.node =
        tree.decoration.node.map morphism) :
    (mapCostRegionTree morphism scope laws tree).decoration =
      tree.decoration.map morphism := by
  apply CostTreeDecoration.ext
  · simp
  · simp
  · simp
  · simp
  · simpa only [CostTreeDecoration.node_map] using nodeEquality

mutual
  /-- Mapping a tree preserves its proof-relevant structural node.  The full
  decoration theorem below adds the four index projections. -/
  private theorem mapCostRegionTree_decoration_node
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (tree : CostRegionTree source targetFree available outer pattern type) :
      (mapCostRegionTree morphism scope laws tree).decoration.node =
        tree.decoration.node.map morphism :=
    match tree with
    | .bvar _ => by
        simp [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map]
    | .fvar _ => by
        simp [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map]
    | .static node children => by
        have childEquality := mapCostRegionBoundaryTrees_decorations
          morphism scope laws children
        simp only [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map,
          CostRegionTree.decoration_reindex,
          CostStaticRegionNode.map_sourceSort]
        congr 1
        · exact CostStaticRegionNode.map_plan_decoration morphism scope laws
            node
        · apply Eq.trans ?_ childEquality
          apply CostRegionBoundaryTrees.decorations_reindexPacket
    | .neutralApplicationOrdinary _ _ constructor _ _ _ children => by
        have childEquality := mapCostRegionArgumentTrees_decorations
          morphism scope laws children
        simp only [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map,
          CostRegionTree.decoration_reindex]
        congr 1
    | .neutralApplicationQuote _ _ constructor _ _ _ children => by
        have childEquality := mapCostRegionArgumentTrees_decorations
          morphism scope laws children
        simp only [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map,
          CostRegionTree.decoration_reindex]
        congr 1
        apply Eq.trans ?_ childEquality
        apply CostRegionArgumentTrees.decorations_reindexOuter
    | .lambda bodyTree => by
        have bodyEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws bodyTree
            (mapCostRegionTree_decoration_node morphism scope laws bodyTree)
        simpa [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map] using
            bodyEquality
    | .multiLambda bodyTree => by
        have bodyEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws bodyTree
            (mapCostRegionTree_decoration_node morphism scope laws bodyTree)
        simpa [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map,
          CostRegionTree.decoration_reindexAvailable] using bodyEquality
    | .subst bodyTree replacementTree => by
        have bodyEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws bodyTree
            (mapCostRegionTree_decoration_node morphism scope laws bodyTree)
        have replacementEquality := mapCostRegionTree_decoration_of_node
          morphism scope laws replacementTree
            (mapCostRegionTree_decoration_node morphism scope laws
              replacementTree)
        simpa [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map] using
            congrArg₂ CostTreeDecorationNode.subst bodyEquality
              replacementEquality
    | .collection children => by
        have childEquality := mapCostRegionElementTrees_decorations morphism
          scope laws children
        simpa [mapCostRegionTree, CostRegionTree.decoration,
          CostTreeDecoration.node, CostTreeDecorationNode.map,
          CostRegionTree.decoration_reindex] using childEquality

  /-- Mapping an argument forest maps its complete decorations pointwise. -/
  theorem mapCostRegionArgumentTrees_decorations
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      (trees : CostRegionArgumentTrees source targetFree available outer
        arguments parameters) :
      (mapCostRegionArgumentTrees morphism scope laws trees).decorations =
        mapCostTreeDecorations morphism trees.decorations :=
    match trees with
    | .nil => by
        simp [mapCostRegionArgumentTrees,
          CostRegionArgumentTrees.decorations, mapCostTreeDecorations]
    | .cons _ _ head tail => by
        have headEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws head
            (mapCostRegionTree_decoration_node morphism scope laws head)
        have tailEquality := mapCostRegionArgumentTrees_decorations morphism
          scope laws tail
        simpa [mapCostRegionArgumentTrees,
          CostRegionArgumentTrees.decorations, mapCostTreeDecorations] using
            congrArg₂ List.cons headEquality tailEquality

  /-- Mapping a collection-element forest maps its complete decorations
  pointwise. -/
  theorem mapCostRegionElementTrees_decorations
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {elements : List Pattern}
      {elementType : TypeExpr}
      (trees : CostRegionElementTrees source targetFree available outer
        elements elementType) :
      (mapCostRegionElementTrees morphism scope laws trees).decorations =
        mapCostTreeDecorations morphism trees.decorations :=
    match trees with
    | .nil _ _ _ => by
        simp [mapCostRegionElementTrees,
          CostRegionElementTrees.decorations, mapCostTreeDecorations]
    | .cons head tail => by
        have headEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws head
            (mapCostRegionTree_decoration_node morphism scope laws head)
        have tailEquality := mapCostRegionElementTrees_decorations morphism
          scope laws tail
        simpa [mapCostRegionElementTrees,
          CostRegionElementTrees.decorations, mapCostTreeDecorations] using
            congrArg₂ List.cons headEquality tailEquality

  /-- Mapping a boundary forest maps each exact occurrence and its child
  decoration without identifying duplicates. -/
  theorem mapCostRegionBoundaryTrees_decorations
      {source target : CIGSLT} (morphism : source.Morphism target)
      (scope : CostGeneratedReflectiveScopePreserving morphism)
      (laws : CostElaborationReindexLaws morphism)
      {targetFree : WellSorted.FreeTypeContext} {color : CostStaticColor}
      {occurrences : List CostRegionOccurrence}
      {table : TypedCostRegionBoundaryTable source color targetFree
        occurrences}
      (trees : CostRegionBoundaryTrees source targetFree color table) :
      (mapCostRegionBoundaryTrees morphism scope laws trees).decorations =
        mapCostBoundaryDecorations morphism trees.decorations :=
    match trees with
    | .nil => by
        simp [mapCostRegionBoundaryTrees,
          CostRegionBoundaryTrees.decorations, mapCostBoundaryDecorations]
    | .cons head children => by
        have headEquality := mapCostRegionTree_decoration_of_node morphism
          scope laws head
            (mapCostRegionTree_decoration_node morphism scope laws head)
        have childEquality := mapCostRegionBoundaryTrees_decorations morphism
          scope laws children
        simp only [mapCostRegionBoundaryTrees,
          CostRegionBoundaryTrees.decorations, mapCostBoundaryDecorations]
        apply congrArg₂ List.cons
        · apply Prod.ext
          · rfl
          · convert headEquality using 1
            rfl
        · exact childEquality
end

/-- Proof-relevant tree mapping is natural with respect to the complete
nondependent decoration projection. -/
theorem mapCostRegionTree_decoration
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (tree : CostRegionTree source targetFree available outer pattern type) :
    (mapCostRegionTree morphism scope laws tree).decoration =
      tree.decoration.map morphism :=
  mapCostRegionTree_decoration_of_node morphism scope laws tree
    (mapCostRegionTree_decoration_node morphism scope laws tree)

/-- Mapping an open elaboration maps its complete computational decoration
exactly. -/
theorem CostOpenElaboration.decoration_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    {term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort}
    (elaboration : CostOpenElaboration source term) :
    (elaboration.map morphism scope laws).decoration =
      elaboration.decoration.map morphism :=
  mapCostRegionTree_decoration morphism scope laws elaboration.tree

/-- Mapping an intrinsically typed Cost term maps its retained decoration
exactly. -/
theorem CostElabTerm.decoration_map
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : CostElabTerm source targetFree targetBound targetSort) :
    (term.map morphism scope laws).decoration =
      term.decoration.map morphism :=
  term.2.decoration_map morphism scope laws

/-- Sigma-bundled Cost fibre transport is natural for the complete retained
decoration. -/
theorem mapCostElaborationFiber_decoration
    {source target : CIGSLT} (morphism : source.Morphism target)
    (scope : CostGeneratedReflectiveScopePreserving morphism)
    (laws : CostElaborationReindexLaws morphism)
    (fiber : CostElaborationFiber source) :
    (mapCostElaborationFiber morphism scope laws fiber).2.decoration =
      fiber.2.decoration.map morphism :=
  CostElabTerm.decoration_map morphism scope laws fiber.2

end Mettapedia.GSLT.LanguageDef
