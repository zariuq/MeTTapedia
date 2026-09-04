import Mettapedia.GSLT.LanguageDef.CostStaticPlanStoppedShape

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: the stopped/reached classification is total for any plan and any
decomposition of its pattern. -/
example {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (fillEq : pattern = context.fill payload) :
    Nonempty (CostStaticPlanStopped source color targetFree payload
        plan.abstractPattern) ∨
      Nonempty (CostStaticPlanReached source color targetFree payload
        plan.abstractPattern) := by
  obtain ⟨⟨view, _shape⟩⟩ := plan.nonempty_shapedContextView context fillEq
  cases view with
  | stopped state => exact .inl ⟨state⟩
  | reached state => exact .inr ⟨state⟩

end Mettapedia.GSLT.LanguageDef
