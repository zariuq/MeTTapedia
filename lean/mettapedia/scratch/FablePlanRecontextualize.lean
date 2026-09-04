import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

mutual
  def CostStaticRegionPlan.recontextualize
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      CostStaticRegionPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable newOuter pattern sourceType :=
    match plan with
    | .bvar sourceIndex lookup correspondence availableScope =>
        .bvar sourceIndex lookup correspondence availableScope
    | .fvar lookup => .fvar lookup
    | .boundaryApplication constructor rendered outsideCurrent certified certifies =>
        .boundaryApplication constructor rendered outsideCurrent certified certifies
    | .application constructor rendered current preimage notBare children =>
        .application constructor rendered current preimage notBare
          (children.recontextualize newOuter)
    | .lambda bodyPlan =>
        .lambda (bodyPlan.recontextualize
          (newOuter.comp (.lambda _ .hole)))
    | .multiLambda bodyPlan =>
        .multiLambda (bodyPlan.recontextualize
          (newOuter.comp (.multiLambda _ _ .hole)))
    | .collection choice selected children =>
        .collection choice selected (children.recontextualize newOuter)
    | .boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        .boundaryCollection currentRejected oppositeChoice oppositeSelected
          certified certifies

  def CostStaticArgumentPlan.recontextualize
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (newOuter : OneHoleContext)
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters) :
      CostStaticArgumentPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable newOuter wireName before arguments parameters :=
    match plan with
    | .nil => .nil
    | @CostStaticArgumentPlan.cons _ _ _ _ _ _ _ _ _ _ argument arguments
        _ _ _ representation parameterType head tail =>
        .cons representation parameterType
          (head.recontextualize
            (newOuter.comp (.apply wireName before .hole arguments)))
          (tail.recontextualize newOuter)

  def CostStaticElementPlan.recontextualize
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType) :
      CostStaticElementPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable newOuter collectionType before elements rest
        sourceElementType :=
    match plan with
    | .nil => .nil
    | @CostStaticElementPlan.cons _ _ _ _ _ _ _ _ _ _ element elements _ _
        head tail =>
        .cons
          (head.recontextualize
            (newOuter.comp
              (.collection collectionType before .hole elements rest)))
          (tail.recontextualize newOuter)
end

mutual
  theorem CostStaticRegionPlan.recontextualize_abstractPattern
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      (plan.recontextualize newOuter).abstractPattern = plan.abstractPattern :=
    match plan with
    | .bvar .. => rfl
    | .fvar .. => rfl
    | .boundaryApplication .. => rfl
    | .application _ _ _ _ _ children =>
        congrArg (Pattern.apply _)
          (children.recontextualize_abstractPatterns newOuter)
    | .lambda bodyPlan =>
        congrArg (Pattern.lambda _)
          (bodyPlan.recontextualize_abstractPattern
            (newOuter.comp (.lambda _ .hole)))
    | .multiLambda bodyPlan =>
        congrArg (Pattern.multiLambda _ _)
          (bodyPlan.recontextualize_abstractPattern
            (newOuter.comp (.multiLambda _ _ .hole)))
    | .collection _ _ children =>
        congrArg (fun elements => Pattern.collection _ elements _)
          (children.recontextualize_abstractPatterns newOuter)
    | .boundaryCollection .. => rfl

  theorem CostStaticArgumentPlan.recontextualize_abstractPatterns
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (newOuter : OneHoleContext)
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters) :
      (plan.recontextualize newOuter).abstractPatterns = plan.abstractPatterns :=
    match plan with
    | .nil => rfl
    | @CostStaticArgumentPlan.cons _ _ _ _ _ _ _ _ _ _ argument arguments
        _ _ _ _ _ head tail =>
        congrArg₂ List.cons
          (head.recontextualize_abstractPattern
            (newOuter.comp (.apply wireName before .hole arguments)))
          (tail.recontextualize_abstractPatterns newOuter)

  theorem CostStaticElementPlan.recontextualize_abstractPatterns
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType) :
      (plan.recontextualize newOuter).abstractPatterns = plan.abstractPatterns :=
    match plan with
    | .nil => rfl
    | @CostStaticElementPlan.cons _ _ _ _ _ _ _ _ _ _ element elements _ _
        head tail =>
        congrArg₂ List.cons
          (head.recontextualize_abstractPattern
            (newOuter.comp
              (.collection collectionType before .hole elements rest)))
          (tail.recontextualize_abstractPatterns newOuter)
end

mutual
  theorem CostStaticRegionPlan.recontextualize_boundaryTable_entries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .bvar .. => rfl
    | .fvar .. => rfl
    | .boundaryApplication .. => rfl
    | .application _ _ _ _ _ children =>
        children.recontextualize_boundaryTable_entries newOuter
    | .lambda bodyPlan =>
        bodyPlan.recontextualize_boundaryTable_entries
          (newOuter.comp (.lambda _ .hole))
    | .multiLambda bodyPlan =>
        bodyPlan.recontextualize_boundaryTable_entries
          (newOuter.comp (.multiLambda _ _ .hole))
    | .collection _ _ children =>
        children.recontextualize_boundaryTable_entries newOuter
    | .boundaryCollection .. => rfl

  theorem CostStaticArgumentPlan.recontextualize_boundaryTable_entries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {wireName : String}
      {before arguments : List Pattern} {parameters : List TermParam}
      (newOuter : OneHoleContext)
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
        parameters) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .nil => rfl
    | @CostStaticArgumentPlan.cons _ _ _ _ _ _ _ _ _ _ argument arguments
        _ _ _ _ _ head tail =>
        by
          change
            ((head.recontextualize
                (newOuter.comp (.apply wireName before .hole arguments))
              ).boundaryTable.append
                (tail.recontextualize newOuter).boundaryTable).entries =
              (head.boundaryTable.append tail.boundaryTable).entries
          rw [TypedCostRegionBoundaryTable.entries_append,
            TypedCostRegionBoundaryTable.entries_append]
          exact congrArg₂ List.append
            (head.recontextualize_boundaryTable_entries
              (newOuter.comp (.apply wireName before .hole arguments)))
            (tail.recontextualize_boundaryTable_entries newOuter)

  theorem CostStaticElementPlan.recontextualize_boundaryTable_entries
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {outer : OneHoleContext} {collectionType : CollType}
      {before elements : List Pattern} {rest : Option String}
      {sourceElementType : TypeExpr}
      (newOuter : OneHoleContext)
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before
        elements rest sourceElementType) :
      (plan.recontextualize newOuter).boundaryTable.entries =
        plan.boundaryTable.entries :=
    match plan with
    | .nil => rfl
    | @CostStaticElementPlan.cons _ _ _ _ _ _ _ _ _ _ element elements _ _
        head tail =>
        by
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
            (head.recontextualize_boundaryTable_entries
              (newOuter.comp
                (.collection collectionType before .hole elements rest)))
            (tail.recontextualize_boundaryTable_entries newOuter)
end

end Mettapedia.GSLT.LanguageDef
