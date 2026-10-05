import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers

/-!
# Retained static spine paths after a prefix replacement

The argument and element planners record the compact prefix preceding each
occurrence.  Replacing an earlier sibling therefore requires recalculating
the paths of later siblings.  These operations preserve their actual plans,
source abstract patterns and ordered boundary certificates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Recalculate the occurrence paths of an existing argument spine under a
new preceding compact prefix.  Argument data and typing remain unchanged. -/
def CostStaticArgumentPlan.reprefix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments parameters)
    (newBefore : List Pattern) :
    CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire newBefore arguments parameters :=
  match plan with
  | .nil => .nil
  | .cons representation parameterType head tail =>
      .cons representation parameterType
        (head.recontextualize
          (outer.comp (.apply wire newBefore .hole _)))
        (tail.reprefix (newBefore ++ [_]))

/-- Prefix replacement preserves the full abstract argument sequence. -/
theorem CostStaticArgumentPlan.reprefix_abstractPatterns
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments parameters)
    (newBefore : List Pattern) :
    (plan.reprefix newBefore).abstractPatterns = plan.abstractPatterns :=
  match plan with
  | .nil => rfl
  | .cons _ _ head tail => by
      simp only [CostStaticArgumentPlan.reprefix,
        CostStaticArgumentPlan.abstractPatterns, List.cons.injEq]
      exact ⟨head.recontextualizeAbstractEq _, tail.reprefix_abstractPatterns _⟩

/-- Prefix replacement preserves the ordered proof-relevant certificate
entries, including duplicate occurrences. -/
theorem CostStaticArgumentPlan.reprefix_entries
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {wire : String}
    {before arguments : List Pattern} {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning available outer wire before arguments parameters)
    (newBefore : List Pattern) :
    (plan.reprefix newBefore).boundaryTable.entries = plan.boundaryTable.entries :=
  match plan with
  | .nil => rfl
  | @CostStaticArgumentPlan.cons _ _ _ _ _ _ _ _ _ _ argument arguments
      _ _ _ _ _ head tail => by
      change ((head.recontextualize
        (outer.comp (.apply wire newBefore .hole arguments))).boundaryTable.append
          (tail.reprefix (newBefore ++ [argument])).boundaryTable).entries =
        (head.boundaryTable.append tail.boundaryTable).entries
      rw [TypedCostRegionBoundaryTable.entries_append,
        TypedCostRegionBoundaryTable.entries_append]
      exact congrArg₂ List.append (head.recontextualizeEntriesEq _)
        (tail.reprefix_entries _)

/-- The corresponding operation for homogeneous collection element spines. -/
def CostStaticElementPlan.reprefix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType before elements rest sourceType)
    (newBefore : List Pattern) :
    CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType newBefore elements rest sourceType :=
  match plan with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.recontextualize
        (outer.comp (.collection collectionType newBefore .hole _ rest)))
        (tail.reprefix (newBefore ++ [_]))

theorem CostStaticElementPlan.reprefix_abstractPatterns
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType before elements rest sourceType)
    (newBefore : List Pattern) :
    (plan.reprefix newBefore).abstractPatterns = plan.abstractPatterns :=
  match plan with
  | .nil => rfl
  | .cons head tail => by
      simp only [CostStaticElementPlan.reprefix,
        CostStaticElementPlan.abstractPatterns, List.cons.injEq]
      exact ⟨head.recontextualizeAbstractEq _, tail.reprefix_abstractPatterns _⟩

theorem CostStaticElementPlan.reprefix_entries
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound available : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {outer : OneHoleContext} {collectionType : CollType}
    {before elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
      thinning available outer collectionType before elements rest sourceType)
    (newBefore : List Pattern) :
    (plan.reprefix newBefore).boundaryTable.entries = plan.boundaryTable.entries :=
  match plan with
  | .nil => rfl
  | @CostStaticElementPlan.cons _ _ _ _ _ _ _ _ _ _ element elements _ _
      head tail => by
      change ((head.recontextualize
        (outer.comp (.collection collectionType newBefore .hole elements rest))
        ).boundaryTable.append
          (tail.reprefix (newBefore ++ [element])).boundaryTable).entries =
        (head.boundaryTable.append tail.boundaryTable).entries
      rw [TypedCostRegionBoundaryTable.entries_append,
        TypedCostRegionBoundaryTable.entries_append]
      exact congrArg₂ List.append (head.recontextualizeEntriesEq _)
        (tail.reprefix_entries _)

end Mettapedia.GSLT.LanguageDef
