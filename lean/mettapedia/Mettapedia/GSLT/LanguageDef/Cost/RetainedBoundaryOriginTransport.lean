import Mettapedia.GSLT.LanguageDef.CostSemanticCarrier
import Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentPrefixRefinement

/-!
# Transport retained children across changed occurrence paths

The table's occurrence origins may change while its ordered typed boundary
entries remain equal.  This module transports the current values and the
existing semantic subtrees to the new table.  The comparison observes each
complete indexed subtree, so frame data and current authored representatives
are preserved as well as patterns and certificate multiplicities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A complete semantic boundary subtree with its support and type indices. -/
abbrev PackedTree (source : CIGSLT) (targetFree : WellSorted.FreeTypeContext) :=
  Σ available : List TypeExpr, Σ pattern : Pattern, Σ type : TypeExpr,
    CostSemanticTree source targetFree available [] pattern type

/-- Observe every complete child in occurrence order. -/
def packedChildren {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    (children : CostSemanticBoundaryTrees source targetFree color table values) :
    List (PackedTree source targetFree) :=
  match children with
  | .nil => []
  | .cons head tail => ⟨_, _, _, head⟩ :: packedChildren tail

/-- Preserve existing typed values and semantic children while changing only
their occurrence origins.  Equality of the ordered certificate entries is
sufficient; occurrence lists need not be equal. -/
def transport {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {oldOccurrences : List CostRegionOccurrence}
    {oldTable : TypedCostRegionBoundaryTable source color targetFree oldOccurrences}
    {oldValues : TypedCostRegionBoundaryTable.Values source color targetFree oldTable}
    (oldChildren : CostSemanticBoundaryTrees source targetFree color oldTable oldValues)
    {newOccurrences : List CostRegionOccurrence}
    (newTable : TypedCostRegionBoundaryTable source color targetFree newOccurrences)
    (equalEntries : newTable.entries = oldTable.entries) :
    Σ newValues : TypedCostRegionBoundaryTable.Values source color targetFree newTable,
      CostSemanticBoundaryTrees source targetFree color newTable newValues :=
  match oldChildren, newTable with
  | .nil, .nil => ⟨.nil, .nil⟩
  | .nil, .cons _ _ _ => by
      simp [TypedCostRegionBoundaryTable.entries] at equalEntries
  | .cons _ _, .nil => by
      simp [TypedCostRegionBoundaryTable.entries] at equalEntries
  | @CostSemanticBoundaryTrees.cons _ _ _ _ _ boundary _ _ value _ head tail,
      .cons newBoundary newContent newTail => by
      have equalHead : newBoundary = boundary := (List.cons.inj equalEntries).1
      have equalTail : newTail.entries = _ := (List.cons.inj equalEntries).2
      cases equalHead
      let retained := transport tail newTail equalTail
      exact ⟨.cons value retained.1, .cons head retained.2⟩

/-- Origin transport preserves the complete ordered child list.  In
particular it neither recompiles descendants nor merges equal occurrences. -/
theorem transport_packedChildren
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {oldOccurrences : List CostRegionOccurrence}
    {oldTable : TypedCostRegionBoundaryTable source color targetFree oldOccurrences}
    {oldValues : TypedCostRegionBoundaryTable.Values source color targetFree oldTable}
    (oldChildren : CostSemanticBoundaryTrees source targetFree color oldTable oldValues)
    {newOccurrences : List CostRegionOccurrence}
    (newTable : TypedCostRegionBoundaryTable source color targetFree newOccurrences)
    (equalEntries : newTable.entries = oldTable.entries) :
    packedChildren (transport oldChildren newTable equalEntries).2 =
      packedChildren oldChildren := by
  induction oldTable generalizing newOccurrences with
  | nil =>
      cases oldValues
      cases oldChildren
      cases newTable with
      | nil => rfl
      | cons => simp [TypedCostRegionBoundaryTable.entries] at equalEntries
  | cons boundary content oldTail inductionHypothesis =>
      cases oldValues with
      | cons value oldValues =>
          cases oldChildren with
          | cons head tail =>
              cases newTable with
              | nil => simp [TypedCostRegionBoundaryTable.entries] at equalEntries
              | cons newBoundary newContent newTail =>
                  have equalHead : newBoundary = boundary :=
                    (List.cons.inj equalEntries).1
                  cases equalHead
                  simp only [transport, packedChildren, List.cons.injEq, true_and]
                  exact inductionHypothesis tail newTail _

/-- Join two existing child forests in the table's exact concatenation order. -/
def append {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree rightTable}
    (left : CostSemanticBoundaryTrees source targetFree color leftTable leftValues)
    (right : CostSemanticBoundaryTrees source targetFree color rightTable rightValues) :
    CostSemanticBoundaryTrees source targetFree color
      (leftTable.append rightTable) (leftValues.append rightValues) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (append tail right)

theorem append_packedChildren
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {color : CostStaticColor} {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree rightTable}
    (left : CostSemanticBoundaryTrees source targetFree color leftTable leftValues)
    (right : CostSemanticBoundaryTrees source targetFree color rightTable rightValues) :
    packedChildren (append left right) = packedChildren left ++ packedChildren right :=
  match left with
  | .nil => rfl
  | .cons head tail => by
      simpa only [append, packedChildren, List.cons_append] using
        congrArg (List.cons ⟨_, _, _, head⟩) (append_packedChildren tail right)

/-- Recalculate an argument tail's paths while preserving its current values
and complete descendants.  The necessary equality is derived from the actual
planner, rather than requested from a caller. -/
def argumentTail {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments parameters)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree plan.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color plan.boundaryTable values)
    (newBefore : List Pattern) :
    Σ newValues : TypedCostRegionBoundaryTable.Values source color targetFree
        (plan.reprefix newBefore).boundaryTable,
      CostSemanticBoundaryTrees source targetFree color
        (plan.reprefix newBefore).boundaryTable newValues :=
  transport children _ (plan.reprefix_entries newBefore)

theorem argumentTail_packedChildren
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments parameters)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree plan.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color plan.boundaryTable values)
    (newBefore : List Pattern) :
    packedChildren (argumentTail plan children newBefore).2 = packedChildren children :=
  transport_packedChildren children _ _

/-- The corresponding retained transport for a collection tail. -/
def elementTail {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType before elements rest sourceType)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree plan.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color plan.boundaryTable values)
    (newBefore : List Pattern) :
    Σ newValues : TypedCostRegionBoundaryTable.Values source color targetFree
        (plan.reprefix newBefore).boundaryTable,
      CostSemanticBoundaryTrees source targetFree color
        (plan.reprefix newBefore).boundaryTable newValues :=
  transport children _ (plan.reprefix_entries newBefore)

theorem elementTail_packedChildren
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType before elements rest sourceType)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree plan.boundaryTable}
    (children : CostSemanticBoundaryTrees source targetFree color plan.boundaryTable values)
    (newBefore : List Pattern) :
    packedChildren (elementTail plan children newBefore).2 = packedChildren children :=
  transport_packedChildren children _ _

end Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport
