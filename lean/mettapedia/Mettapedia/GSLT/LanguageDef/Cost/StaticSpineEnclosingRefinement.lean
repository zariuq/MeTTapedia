import Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport

/-!
# Enclosing a refined retained spine

Refining a later argument changes the suffix in every earlier argument's
occurrence context.  These enclosing steps recalculate those contexts,
preserve all earlier certificates and current semantic subtrees, and attach
the supplied refined tail.  Argument and collection spines use their existing
indexed planners and exact finite child forests.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open RetainedBoundaryOriginTransport

namespace Argument

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext}
  {sourceBound targetBound available : List TypeExpr}
  {thinning : CostStaticBinderThinning source color sourceBound targetBound}
  {outer : OneHoleContext} {wire : String} {before : List Pattern}
  {argument : Pattern} {oldTailArguments newTailArguments : List Pattern}
  {parameter : TermParam} {parameters : List TermParam} {sourceType : TypeExpr}
  (representation : WellSorted.MatchesParameterRepresentation parameter argument)
  (parameterType : WellSorted.parameterType? parameter = some sourceType)
  (head : CostStaticRegionPlan source color targetFree sourceBound targetBound
    thinning available (outer.comp (.apply wire before .hole oldTailArguments))
    argument sourceType)
  (tail : CostStaticArgumentPlan source color targetFree sourceBound targetBound
    thinning available outer wire (before ++ [argument]) newTailArguments parameters)

/-- Retain the existing head and enclose the supplied refined tail. -/
def plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
    thinning available outer wire before (argument :: newTailArguments)
    (parameter :: parameters) :=
  .cons representation parameterType
    (head.recontextualize (outer.comp (.apply wire before .hole newTailArguments))) tail

theorem entries :
    (plan representation parameterType head tail).boundaryTable.entries =
      head.boundaryTable.entries ++ tail.boundaryTable.entries := by
  change ((head.recontextualize _).boundaryTable.append tail.boundaryTable).entries = _
  rw [TypedCostRegionBoundaryTable.entries_append, head.recontextualizeEntriesEq]

theorem abstractPatterns :
    (plan representation parameterType head tail).abstractPatterns =
      head.abstractPattern :: tail.abstractPatterns := by
  change (head.recontextualize _).abstractPattern :: _ = _
  rw [head.recontextualizeAbstractEq]

variable {headValues : TypedCostRegionBoundaryTable.Values source color targetFree
    head.boundaryTable}
  {tailValues : TypedCostRegionBoundaryTable.Values source color targetFree tail.boundaryTable}
  (headChildren : CostSemanticBoundaryTrees source targetFree color head.boundaryTable headValues)
  (tailChildren : CostSemanticBoundaryTrees source targetFree color tail.boundaryTable tailValues)

/-- Recontextualize only the retained head's origins, then join it with the
supplied refined tail without changing either complete subtree list. -/
def children :
    Σ values : TypedCostRegionBoundaryTable.Values source color targetFree
        (plan representation parameterType head tail).boundaryTable,
      CostSemanticBoundaryTrees source targetFree color
        (plan representation parameterType head tail).boundaryTable values := by
  let newHead := transport headChildren
    (head.recontextualize (outer.comp (.apply wire before .hole newTailArguments))).boundaryTable
    (head.recontextualizeEntriesEq _)
  exact ⟨_, RetainedBoundaryOriginTransport.append newHead.2 tailChildren⟩

theorem children_packedChildren :
    packedChildren (children representation parameterType head tail
      headChildren tailChildren).2 =
      packedChildren headChildren ++ packedChildren tailChildren := by
  change packedChildren (RetainedBoundaryOriginTransport.append
    (transport headChildren
      (head.recontextualize (outer.comp (.apply wire before .hole newTailArguments))).boundaryTable
      (head.recontextualizeEntriesEq _)).2 tailChildren) = _
  rw [append_packedChildren, transport_packedChildren]

end Argument

namespace Element

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext}
  {sourceBound targetBound available : List TypeExpr}
  {thinning : CostStaticBinderThinning source color sourceBound targetBound}
  {outer : OneHoleContext} {collectionType : CollType} {before : List Pattern}
  {element : Pattern} {oldTailElements newTailElements : List Pattern}
  {rest : Option String} {sourceType : TypeExpr}
  (head : CostStaticRegionPlan source color targetFree sourceBound targetBound
    thinning available
    (outer.comp (.collection collectionType before .hole oldTailElements rest))
    element sourceType)
  (tail : CostStaticElementPlan source color targetFree sourceBound targetBound
    thinning available outer collectionType (before ++ [element])
    newTailElements rest sourceType)

def plan : CostStaticElementPlan source color targetFree sourceBound targetBound
    thinning available outer collectionType before (element :: newTailElements) rest sourceType :=
  .cons
    (head.recontextualize
      (outer.comp (.collection collectionType before .hole newTailElements rest))) tail

theorem entries :
    (plan head tail).boundaryTable.entries =
      head.boundaryTable.entries ++ tail.boundaryTable.entries := by
  change ((head.recontextualize _).boundaryTable.append tail.boundaryTable).entries = _
  rw [TypedCostRegionBoundaryTable.entries_append, head.recontextualizeEntriesEq]

theorem abstractPatterns :
    (plan head tail).abstractPatterns = head.abstractPattern :: tail.abstractPatterns := by
  change (head.recontextualize _).abstractPattern :: _ = _
  rw [head.recontextualizeAbstractEq]

variable {headValues : TypedCostRegionBoundaryTable.Values source color targetFree
    head.boundaryTable}
  {tailValues : TypedCostRegionBoundaryTable.Values source color targetFree tail.boundaryTable}
  (headChildren : CostSemanticBoundaryTrees source targetFree color head.boundaryTable headValues)
  (tailChildren : CostSemanticBoundaryTrees source targetFree color tail.boundaryTable tailValues)

def children :
    Σ values : TypedCostRegionBoundaryTable.Values source color targetFree (plan head tail).boundaryTable,
      CostSemanticBoundaryTrees source targetFree color (plan head tail).boundaryTable values := by
  let newHead := transport headChildren
    (head.recontextualize
      (outer.comp (.collection collectionType before .hole newTailElements rest))).boundaryTable
    (head.recontextualizeEntriesEq _)
  exact ⟨_, RetainedBoundaryOriginTransport.append newHead.2 tailChildren⟩

theorem children_packedChildren :
    packedChildren (children head tail headChildren tailChildren).2 =
      packedChildren headChildren ++ packedChildren tailChildren := by
  change packedChildren (RetainedBoundaryOriginTransport.append
    (transport headChildren
      (head.recontextualize
        (outer.comp (.collection collectionType before .hole newTailElements rest))).boundaryTable
      (head.recontextualizeEntriesEq _)).2 tailChildren) = _
  rw [append_packedChildren, transport_packedChildren]

end Element

#print axioms Argument.plan
#print axioms Argument.entries
#print axioms Argument.abstractPatterns
#print axioms Argument.children
#print axioms Argument.children_packedChildren
#print axioms Element.plan
#print axioms Element.entries
#print axioms Element.abstractPatterns
#print axioms Element.children
#print axioms Element.children_packedChildren

end Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement
