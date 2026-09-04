import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticCollapseExposure
import Mettapedia.GSLT.LanguageDef.CostStaticPlanStoppedShape

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PROBE: obtain the stopped/reached classification for a static root view's
own plan, decomposed at a chosen payload. -/
example {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (payload : Pattern)
    (fillEq : leftView.node.term.1 = context.fill payload) :
    Nonempty (CostStaticPlanStopped rhoCIGSLT color targetFree payload
        leftView.node.plan.abstractPattern) ∨
      Nonempty (CostStaticPlanReached rhoCIGSLT color targetFree payload
        leftView.node.plan.abstractPattern) := by
  obtain ⟨⟨view, _shape⟩⟩ :=
    leftView.node.plan.nonempty_shapedContextView context fillEq
  cases view with
  | stopped state => exact .inl ⟨state⟩
  | reached state => exact .inr ⟨state⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
