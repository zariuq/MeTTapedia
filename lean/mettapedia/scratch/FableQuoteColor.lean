import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.GSLT.LanguageDef.CostStaticPlanCanonicalAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ReflectionExtension

private theorem rhoCost_application_declarationColor_eq
    (declarationColor color : CostStaticColor)
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    {wireName : String}
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor = wireName)
    (wireEq : wireName =
      declarationColor.constructorTag ++
        rhoReflectivePresentation.quoteConstructor)
    (preimage : CostStaticConstructorPreimage rhoCIGSLT color constructor) :
    declarationColor = color := by
  have mappedEq :
      (color.symbols rhoCIGSLT).constructor
          preimage.sourceConstructor.1.label =
        (declarationColor.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor := by
    rw [← preimage.labelMap,
      rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered, wireEq]
    cases declarationColor <;> rfl
  cases declarationColor <;> cases color
  · rfl
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq.symm)
  · exact False.elim (costBaseConstructorName_ne_wrapped _ _ mappedEq)
  · rfl

/-- A reached source Quote that is a collapsing root for a generated rho
declaration can only belong to that same generated colour. -/
theorem CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (sourceQuote : state.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      payload) :
    declarationColor = color := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;>
    rcases collapsing with ⟨arguments, shape⟩ | ⟨elements, shape⟩ <;>
    simp [costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] at shape
  all_goals simp_all [CostStaticRegionPlan.rootClass]
  all_goals rcases shape with ⟨shape, _⟩
  apply rhoCost_application_declarationColor_eq
  all_goals assumption

/-- The payload of a reached source-Quote plan is literally a Quote under the
generated declaration of the selected colour. -/
theorem CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (sourceQuote : state.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor) :
    ∃ arguments,
      payload = .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).quoteConstructor arguments := by
  rcases state with
    ⟨sourceBound, targetBound, thinning, sourceAvailable, outer, sourceType,
      plan, skeletonContext, abstractEq⟩
  cases plan <;> simp_all [CostStaticRegionPlan.rootClass]
  case application wireName arguments constructor rendered current preimage
      notBare children =>
    simp only [mapReflectivePresentation]
    rw [← sourceQuote]
    simp only [CostStaticColor.reflectiveSymbols_constructor]
    rw [← preimage.labelMap,
      rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered]

/-- At a same-colour reached Quote pair, canonical stop alignment cannot use
the rigid application arm: the generated constructor is the declaration's
own Quote. Therefore the alignment is exactly the delegated stop. -/
theorem CanonicalStopAligned.stop_of_reached_sourceQuotes
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    {stop : Pattern → Pattern → Prop}
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation) stop leftPayload rightPayload) :
    stop leftPayload rightPayload := by
  obtain ⟨leftArguments, leftShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      leftReached leftQuote
  obtain ⟨rightArguments, rightShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      rightReached rightQuote
  rw [leftShape, rightShape] at aligned ⊢
  cases aligned with
  | leaf given => exact given
  | apply ne _ => exact False.elim (ne rfl)

/-- Exact colour split for a reached source-Quote pair.  A delegated stop
whose witness is collapsing must be same-colour.  Otherwise the only possible
foreign-colour alignment is rigid descent through the generated Quote's
argument list. -/
theorem CanonicalStopAligned.reached_sourceQuotes_cases
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    {stop : Pattern → Pattern → Prop}
    (stopCollapsing : ∀ {left right}, stop left right →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (aligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation) stop leftPayload rightPayload) :
    (declarationColor = color ∧ stop leftPayload rightPayload) ∨
      (declarationColor = color.flip ∧
        ∃ leftArguments rightArguments,
          leftPayload = .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor leftArguments ∧
          rightPayload = .apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor rightArguments ∧
          CanonicalStopAlignedList
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) stop leftArguments rightArguments) := by
  obtain ⟨leftArguments, leftShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      leftReached leftQuote
  obtain ⟨rightArguments, rightShape⟩ :=
    CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
      rightReached rightQuote
  subst leftPayload
  subst rightPayload
  cases aligned with
  | leaf given =>
      rcases stopCollapsing given with leftCollapsing | rightCollapsing
      · exact Or.inl ⟨
          CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            leftReached leftQuote leftCollapsing,
          given⟩
      · exact Or.inl ⟨
          CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            rightReached rightQuote rightCollapsing,
          given⟩
  | apply ne children =>
      refine Or.inr ⟨CostStaticColor.eq_flip_of_ne ?_, leftArguments,
        rightArguments, rfl, rfl, children⟩
      intro colorEq
      subst declarationColor
      exact ne rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
