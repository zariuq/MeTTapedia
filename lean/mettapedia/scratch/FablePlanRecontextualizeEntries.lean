import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

mutual
  theorem CostStaticRegionPlan.recontextualizeEntriesEqTest
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (newOuter : OneHoleContext) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .bvar .. => rfl
    | .fvar .. => rfl
    | .boundaryApplication .. => rfl
    | .application _ _ _ _ _ children =>
        children.recontextualizeEntriesEqTest newOuter
    | .lambda bodyPlan =>
        bodyPlan.recontextualizeEntriesEqTest
          (newOuter.comp (.lambda _ .hole))
    | .multiLambda bodyPlan =>
        bodyPlan.recontextualizeEntriesEqTest
          (newOuter.comp (.multiLambda _ _ .hole))
    | .collection _ _ children =>
        children.recontextualizeEntriesEqTest newOuter
    | .boundaryCollection .. => rfl

  theorem CostStaticArgumentPlan.recontextualizeEntriesEqTest
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters)
      (newOuter : OneHoleContext) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .nil => rfl
    | @CostStaticArgumentPlan.cons _ _ _ _ _ _ _ _ _ _ argument arguments
        _ _ _ _ _ head tail => by
        change
          ((head.recontextualize
              (newOuter.comp (.apply wireName before .hole arguments))
            ).boundaryTable.append
              (tail.recontextualize newOuter).boundaryTable).entries =
            (head.boundaryTable.append tail.boundaryTable).entries
        rw [TypedCostRegionBoundaryTable.entries_append,
          TypedCostRegionBoundaryTable.entries_append]
        exact congrArg₂ List.append
          (head.recontextualizeEntriesEqTest
            (newOuter.comp (.apply wireName before .hole arguments)))
          (tail.recontextualizeEntriesEqTest newOuter)

  theorem CostStaticElementPlan.recontextualizeEntriesEqTest
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType)
      (newOuter : OneHoleContext) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .nil => rfl
    | @CostStaticElementPlan.cons _ _ _ _ _ _ _ _ _ _ element elements _ _
        head tail => by
        change
          ((head.recontextualize
              (newOuter.comp
                (.collection collectionType before .hole elements rest))
            ).boundaryTable.append
              (tail.recontextualize newOuter).boundaryTable).entries =
            (head.boundaryTable.append tail.boundaryTable).entries
        rw [TypedCostRegionBoundaryTable.entries_append,
          TypedCostRegionBoundaryTable.entries_append]
        exact congrArg₂ List.append
          (head.recontextualizeEntriesEqTest
            (newOuter.comp
              (.collection collectionType before .hole elements rest)))
          (tail.recontextualizeEntriesEqTest newOuter)
end

end Mettapedia.GSLT.LanguageDef
