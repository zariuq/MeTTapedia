import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- A Quote-root static plan is reflectively safe at the reset depth. -/
theorem CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot_canary
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor) :
    binderSafeAt rhoReflectivePresentation.quoteConstructor 0
      plan.abstractPattern = true := by
  have safe := plan.abstractPattern_reflectiveScopeSafeAt
    rhoReflectivePresentation.toReflectivePresentationDecl (by
      change rhoReflectivePresentation.toReflectivePresentationDecl ∈
        ReflectionExtension.rhoReflectionProfile.presentations
      simp [ReflectionExtension.rhoReflectionProfile])
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have sourceQuote : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using quoteRoot
      have paramsLength : preimage.sourceConstructor.1.params.length = 1 :=
        CostHereditaryCrossColorLeafHinge.rhoCalc_params_length_eq_one_of_label_eq_quote
          preimage.sourceConstructor.2 (by
            simpa [rhoReflectivePresentation] using sourceQuote)
      obtain ⟨abstractLength, argumentsLength⟩ :=
        CostHereditaryCrossColorLeafHinge.CostStaticArgumentPlan.abstractPatterns_length
          children
      obtain ⟨child, childShape⟩ := List.length_eq_one_iff.mp
        (abstractLength.trans (argumentsLength.trans paramsLength))
      simp only [CostStaticRegionPlan.abstractPattern] at safe ⊢
      rw [childShape] at safe ⊢
      simpa [binderSafeAt, sourceQuote] using safe
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- Parent-environment canonicalization of an embedded Quote frame is
independent of both semantic-key depths. -/
theorem CostStaticPlanReached.parentCanonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_quoteRoot_canary
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries node.plan.boundaryTable.entries)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt node environment)
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern) =
      canonicalizeByDepths
        (fun _ _ pattern =>
          CostStaticRegionNode.semanticPatternKeyAt environment 0
            (mapPattern (color.symbols rhoCIGSLT) pattern))
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern) := by
  have sourceBase : ∃ category, reached.sourceType = .base category := by
    rcases rho_applicationPlan_sourceType_name_or_proc reached.plan
        ⟨rhoReflectivePresentation.quoteConstructor, quoteRoot⟩ with
      name | process
    · exact ⟨"Name", name⟩
    · exact ⟨"Proc", process⟩
  have frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      reached.plan.abstractPattern = true :=
    CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
      reached.plan sourceBase
  apply
    CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_freeAtomTargetSupport_eq_nil
      node environment availableDepth scopeDepth 0
        (environment.reify reached.plan.abstractPattern)
  · intro name membership slot selected
    exact CostStaticPlanReached.parentAtomTargetSupport_eq_nil_of_quoteRoot
      node reached admission frameFree quoteRoot embedding environment
        membership slot selected
  · rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      reached.plan quoteRoot
  · exact Nat.zero_le _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
