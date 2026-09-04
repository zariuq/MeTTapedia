import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem CostStaticRegionPlan.rigid_cases_typed_canary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rigid : plan.rootClass = .rigid) :
    (∃ index sourceIndex, pattern = .bvar index ∧
        plan.abstractPattern = .bvar sourceIndex) ∨
      (∃ name, pattern = .fvar name ∧
        plan.abstractPattern = .fvar (costRegionSourceVariableName name) ∧
        targetFree name =
          some (mapTypeExpr (color.symbols source) sourceType)) ∨
      (∃ binder body abstractBody domain codomain,
        pattern = .lambda binder body ∧
        plan.abstractPattern = .lambda binder abstractBody ∧
        sourceType = .arrow domain codomain) ∨
      (∃ arity binders body abstractBody domain codomain,
        pattern = .multiLambda arity binders body ∧
        plan.abstractPattern = .multiLambda arity binders abstractBody ∧
        sourceType = .arrow (.multiBinder domain) codomain) := by
  cases plan
  case bvar sourceIndex lookup correspondence availableScope =>
      exact Or.inl ⟨_, sourceIndex, rfl, rfl⟩
  case fvar lookup => exact Or.inr (Or.inl ⟨_, rfl, rfl, lookup⟩)
  case lambda bodyPlan =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩))
  case multiLambda bodyPlan =>
      exact Or.inr (Or.inr (Or.inr
        ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩))
  all_goals simp [CostStaticRegionPlan.rootClass] at rigid

theorem boundarySide_rigidPartner_is_sourceVariable_canary
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {parentMeasure : Nat}
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary)
    (rightRigid : rightReached.plan.rootClass = .rigid)
    (stopReason :
      RhoCanonicalRawStop declarationColor parentMeasure leftPayload
          rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan) :
    ∃ name,
      rightPayload = .fvar name ∧
      rightReached.plan.abstractPattern =
        .fvar (costRegionSourceVariableName name) ∧
      targetFree name = some
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) := by
  rcases CostStaticRegionPlan.rigid_cases_typed_canary rightReached.plan
      rightRigid with
    ⟨index, sourceIndex, payloadEq, abstractEq⟩ |
    ⟨name, payloadEq, abstractEq, lookup⟩ |
    ⟨binder, body, abstractBody, domain, codomain, payloadEq, abstractEq,
      rightTypeEq⟩ |
    ⟨arity, binders, body, abstractBody, domain, codomain, payloadEq,
      abstractEq, rightTypeEq⟩
  · exact (rho_planStop_boundarySide_bvarPartner_absurd leftReached
      rightReached leftBoundary rightRigid ⟨sourceIndex, abstractEq⟩
      stopReason).elim
  · exact ⟨name, payloadEq, abstractEq, lookup⟩
  · exact
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
        leftReached.plan leftBoundary domain codomain
          (sourceTypeEq.trans rightTypeEq)).elim
  · exact
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.sourceType_ne_arrow_of_isCertifiedBoundary
        leftReached.plan leftBoundary (.multiBinder domain) codomain
          (sourceTypeEq.trans rightTypeEq)).elim

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
