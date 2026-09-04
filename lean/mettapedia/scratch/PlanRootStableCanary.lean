import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem rootClass_ne_quote_of_abstractPattern_ne_quote
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern sourceType)
    {quote : String}
    (notQuote : ∀ arguments, plan.abstractPattern ≠ .apply quote arguments) :
    plan.rootClass ≠ .application quote := by
  intro rootClass
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticRegionPlan.abstractPattern] at rootClass notQuote
  contradiction

theorem rootClass_ne_parallel_of_abstractPattern_ne_parallel
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern sourceType)
    {parallel : CollType}
    (admission : plan.RawAdmission)
    (notParallel : ∀ elements,
      plan.abstractPattern ≠ .collection parallel elements none) :
    plan.rootClass ≠ .collection parallel := by
  intro rootClass
  have object := admission.object
  cases plan <;>
    simp [CostStaticRegionPlan.rootClass,
      CostStaticRegionPlan.abstractPattern, WellSorted.isObjectPattern]
      at rootClass notParallel object
  exact (notParallel rootClass) object.1

theorem CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    {collectionType : CollType}
    (rootClass : reached.plan.rootClass = .collection collectionType) :
    ∃ elements, payload = .collection collectionType elements none := by
  rcases reached with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  change plan.RawAdmission at admission
  change plan.rootClass = .collection collectionType at rootClass
  have object := admission.object
  cases plan with
  | collection choice selected children =>
      rename_i actualCollection elements rest
      simp only [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.collection.injEq] at rootClass
      subst actualCollection
      have restNone : rest = none := by
        cases rest with
        | none => rfl
        | some rest => simp [WellSorted.isObjectPattern] at object
      subst rest
      exact ⟨elements, rfl⟩
  | boundaryApplication | boundaryCollection | bvar | fvar | application |
      lambda | multiLambda =>
      simp [CostStaticRegionPlan.rootClass] at rootClass

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
