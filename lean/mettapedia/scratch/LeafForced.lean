import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryNonBoundaryPlanStop

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem PatternLeafAligned.of_fvar_left
    {relation : Pattern → Pattern → Prop} {name : String} {right : Pattern}
    (aligned : PatternLeafAligned relation (.fvar name) right) :
    relation (.fvar name) right := by
  cases aligned with
  | leaf related => exact related

theorem abstractPattern_eq_fvar_of_isCertifiedBoundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) :
    ∃ name, plan.abstractPattern = .fvar name := by
  cases plan <;>
    first
      | exact ⟨_, rfl⟩
      | simp [CostStaticPlanRootClass.IsCertifiedBoundary,
          CostStaticRegionPlan.rootClass] at boundaryClass

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
