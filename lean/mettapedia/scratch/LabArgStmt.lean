import Mettapedia.GSLT.LanguageDef.CostStaticPlanParallelChildren

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- PROBE: does the application analogue's statement elaborate? -/
theorem CostStaticArgumentPlan.abstractPatterns_eq_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {params : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      params)
    (h : params = []) :
    plan.abstractPatterns = [] := by
  subst h
  cases plan
  rfl

theorem CostStaticArgumentPlan.abstractPatterns_eq_cons
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {wireName : String} {before : List Pattern}
    {argument : Pattern} {arguments : List Pattern}
    {parameters : List TermParam}
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before
      (argument :: arguments) parameters) :
    ∃ (sourceExpected : TypeExpr)
      (parameters' : List TermParam)
      (head : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable
        (outer.comp (.apply wireName before .hole arguments))
        argument sourceExpected)
      (tail : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName
        (before ++ [argument]) arguments parameters'),
      plan.abstractPatterns
        = head.abstractPattern :: tail.abstractPatterns := by
  cases plan with
  | cons representation parameterType head tail =>
      exact ⟨_, _, head, tail, rfl⟩

theorem CostStaticRegionPlan.applicationChildrenCanonicalStopAligned_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {leftAvailable rightAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {wireName label : String}
    {leftArguments rightArguments : List Pattern}
    {leftSourceType rightSourceType : TypeExpr}
    (leftPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning leftAvailable leftOuter
      (.apply wireName leftArguments) leftSourceType)
    (rightPlan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning rightAvailable rightOuter
      (.apply wireName rightArguments) rightSourceType)
    (typeEq : leftSourceType = rightSourceType)
    (leftClass : leftPlan.rootClass = .application label)
    (rightClass : rightPlan.rootClass = .application label)
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (availableEq : leftAvailable = rightAvailable)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop
      (.apply wireName leftArguments) (.apply wireName rightArguments))
    (notDelegated : ¬ ∃ stopped,
      rawAligned = CanonicalStopAligned.leaf stopped) :
    ∃ leftAbstracts rightAbstracts,
      leftPlan.abstractPattern = .apply label leftAbstracts ∧
        rightPlan.abstractPattern = .apply label rightAbstracts ∧
        CanonicalStopAlignedList declaration
          (CostStaticPlanCanonicalStopBelow leftPlan rightPlan declaration
            rawDeclaration rawStop
            (sizeOf (Pattern.apply wireName leftArguments) +
              sizeOf (Pattern.apply wireName rightArguments)))
          leftAbstracts rightAbstracts := by
  cases rawAligned with
  | leaf given => exact (notDelegated ⟨given, rfl⟩).elim
  | apply rawNe argumentsAligned =>
      cases leftPlan with
      | boundaryApplication leftRejected leftOpposite leftOppositeSelected
          leftCertified leftCertifies =>
          simp [CostStaticRegionPlan.rootClass] at leftClass
      | application leftConstructor leftRendered leftCurrent leftPreimage
          leftNotBare leftChildren =>
          cases rightPlan with
          | boundaryApplication rightRejected rightOpposite
              rightOppositeSelected rightCertified rightCertifies =>
              simp [CostStaticRegionPlan.rootClass] at rightClass
          | application rightConstructor rightRendered rightCurrent
              rightPreimage rightNotBare rightChildren =>
              simp only [CostStaticRegionPlan.rootClass,
                CostStaticPlanRootClass.application.injEq] at leftClass rightClass
              subst leftClass
              refine ⟨leftChildren.abstractPatterns,
                rightChildren.abstractPatterns, rfl, ?_, ?_⟩
              · simp only [CostStaticRegionPlan.abstractPattern, rightClass]
              · cases argumentsAligned with
                | nil =>
                    obtain ⟨rule, ruleMem, labelEq, notBareRule, typeEqRule,
                      argsTyped⟩ :=
                      WellSorted.hasType_apply_inversion
                        leftAdmission.wellSorted.1.1
                    have lengthEq := argsTyped.length_eq
                    have ruleEq : rule =
                        source.materializeDeclaredCostConstructor
                          leftConstructor := by
                      apply CIGSLT.costWholeLanguage_labelDeterministic source
                        ruleMem
                      · obtain ⟨kind, kindProof⟩ := leftConstructor
                        cases kind with
                        | base c =>
                            exact CIGSLT.costBaseConstructor_mem_costWhole source _ c.2
                        | wrapped c =>
                            exact CIGSLT.costWrappedConstructor_mem_costWhole source _ kindProof
                        | apparatus k =>
                            simp [CIGSLT.declaredCostConstructorRole] at leftCurrent
                      · rw [← labelEq, ← leftRendered,
                          CIGSLT.materializeDeclaredCostConstructor_label]
                    subst ruleEq
                    rw [leftPreimage.parametersMap] at lengthEq
                    simp at lengthEq
                    have paramsNil :
                        leftPreimage.sourceConstructor.1.params = [] :=
                      List.eq_nil_of_length_eq_zero lengthEq.symm
                    obtain ⟨rrule, rruleMem, rlabelEq, _, _, rargsTyped⟩ :=
                      WellSorted.hasType_apply_inversion
                        rightAdmission.wellSorted.1.1
                    have rlengthEq := rargsTyped.length_eq
                    have rruleEq : rrule =
                        source.materializeDeclaredCostConstructor
                          rightConstructor := by
                      apply CIGSLT.costWholeLanguage_labelDeterministic source
                        rruleMem
                      · obtain ⟨kind, kindProof⟩ := rightConstructor
                        cases kind with
                        | base c =>
                            exact CIGSLT.costBaseConstructor_mem_costWhole source _ c.2
                        | wrapped c =>
                            exact CIGSLT.costWrappedConstructor_mem_costWhole source _ kindProof
                        | apparatus k =>
                            simp [CIGSLT.declaredCostConstructorRole] at rightCurrent
                      · rw [← rlabelEq, ← rightRendered,
                          CIGSLT.materializeDeclaredCostConstructor_label]
                    subst rruleEq
                    rw [rightPreimage.parametersMap] at rlengthEq
                    simp at rlengthEq
                    have rparamsNil :
                        rightPreimage.sourceConstructor.1.params = [] :=
                      List.eq_nil_of_length_eq_zero rlengthEq.symm
                    rw [CostStaticArgumentPlan.abstractPatterns_eq_nil
                          leftChildren paramsNil,
                        CostStaticArgumentPlan.abstractPatterns_eq_nil
                          rightChildren rparamsNil]
                    exact .nil
                | cons headAligned tailAligned => skip

end Mettapedia.GSLT.LanguageDef
