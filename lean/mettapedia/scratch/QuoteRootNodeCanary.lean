import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A Quote-root plan exposes the exact generated static application data at
its payload index. -/
theorem CostStaticRegionPlan.staticApplicationData_of_quoteRoot_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ wireName arguments constructor,
      pattern = .apply wireName arguments ∧
      rhoCIGSLT.decodeDeclaredCostConstructor wireName = some constructor ∧
      rhoCIGSLT.declaredCostConstructorRole constructor = .static color := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      refine ⟨_, _, constructor, rfl, ?_, current⟩
      rw [← rendered]
      exact rhoCIGSLT.decodeDeclaredCostConstructor_render constructor
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- An admitted reached Quote has a visible-root static plan related to the
contextual reached plan by the exact sealed suffix. -/
theorem CostStaticPlanReached.exists_staticRootPlanSealedAlignment_of_quoteRoot_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ (sealed : List TypeExpr)
        (rootPlan : CostStaticRegionPlan rhoCIGSLT color targetFree
          (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable
          (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
            reached.sourceAvailable)
          reached.sourceAvailable .hole payload reached.sourceType),
      reached.targetBound = reached.sourceAvailable ++ sealed ∧
      rootPlan.CompilerReceipt ∧
      rootPlan.isStaticRoot = true ∧
      CostStaticRegionPlan.BoundaryFibersAvailabilitySuffix sealed .sealed
        rootPlan (reached.plan.recontextualize .hole) := by
  obtain ⟨sealed, rootPlan, split, rootBuilt, aligned⟩ :=
    reached.exists_rootPlanSealedAlignment
      CostCanonicalLaws.rho_unambiguousStaticDecomposition.collectionGloballyUnambiguous
      admission
  obtain ⟨wireName, arguments, constructor, payloadEq, decoded, role⟩ :=
    CostStaticRegionPlan.staticApplicationData_of_quoteRoot_canary
      reached.plan quoteRoot
  let planFamily := fun pattern =>
    CostStaticRegionPlan rhoCIGSLT color targetFree
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT color
        reached.sourceAvailable)
      reached.sourceAvailable
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color
        reached.sourceAvailable)
      reached.sourceAvailable .hole pattern reached.sourceType
  let applicationPlan : planFamily (.apply wireName arguments) :=
    Eq.mp (congrArg planFamily payloadEq) rootPlan
  have applicationPlanStatic : applicationPlan.isStaticRoot = true :=
    applicationPlan.isStaticRoot_of_current_application constructor decoded
      role
  have transportStatic : applicationPlan.isStaticRoot = rootPlan.isStaticRoot := by
    cases payloadEq
    rfl
  have rootStatic : rootPlan.isStaticRoot = true := by
    rw [← transportStatic]
    exact applicationPlanStatic
  exact ⟨sealed, rootPlan, split, rootBuilt, rootStatic, aligned⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
