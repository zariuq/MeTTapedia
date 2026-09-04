import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

example {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern (.base "Proc")) :
    True := by
  generalize sourceTypeEq : TypeExpr.base "Proc" = sourceType at plan
  cases plan with
  | collection choice selected children =>
      rename_i collectionType elements rest
      have selectedProc : choice ∈ costStaticCollectionTypingChoices
          rhoCIGSLT color targetFree targetBound collectionType elements
          (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
        rw [sourceTypeEq]
        exact selected
      have elementType := rho_process_collection_choice_sourceElementType
        color choice selectedProc
      let processChildren := children.castSourceElementType elementType.symm
      trivial
  | bvar => trivial
  | fvar => trivial
  | boundaryApplication => trivial
  | application => trivial
  | lambda => exact TypeExpr.noConfusion sourceTypeEq
  | multiLambda => exact TypeExpr.noConfusion sourceTypeEq
  | boundaryCollection => trivial

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
