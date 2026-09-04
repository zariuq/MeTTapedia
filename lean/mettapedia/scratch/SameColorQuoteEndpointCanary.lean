import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySameColorReachedPairApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignPlanStopRestoration

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The authored rho quotation has exactly one process parameter. -/
theorem rhoCalc_params_eq_singleton_process_of_label_eq_quote
    (rule : StructuralMorphism.AuthoredConstructor
      rhoIGSLT.presentation.presentation)
    (label : rule.1.label = rhoReflectivePresentation.quoteConstructor) :
    rule.1.params = [.simple "p" (.base "Proc")] := by
  have membership := rule.2
  change rule.1 ∈ rhoCalc.terms at membership
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | fifth | sixth
  all_goals
    first
    | rw [first] at label ⊢
    | rw [second] at label ⊢
    | rw [third] at label ⊢
    | rw [fourth] at label ⊢
    | rw [fifth] at label ⊢
    | rw [sixth] at label ⊢
  all_goals
    simp_all [rhoReflectivePresentation, TypeExpr.proc, TypeExpr.baseType]

/-- The authored rho Drop has exactly one name parameter. -/
theorem rhoCalc_params_eq_singleton_name_of_label_eq_drop
    (rule : StructuralMorphism.AuthoredConstructor
      rhoIGSLT.presentation.presentation)
    (label : rule.1.label = rhoReflectivePresentation.dropConstructor) :
    rule.1.params = [.simple "n" (.base "Name")] := by
  have membership := rule.2
  change rule.1 ∈ rhoCalc.terms at membership
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with first | second | third | fourth | fifth | sixth
  all_goals
    first
    | rw [first] at label ⊢
    | rw [second] at label ⊢
    | rw [third] at label ⊢
    | rw [fourth] at label ⊢
    | rw [fifth] at label ⊢
    | rw [sixth] at label ⊢
  all_goals
    simp_all [rhoReflectivePresentation, TypeExpr.name, TypeExpr.baseType]

/-- The exact authored rho Drop constructor. -/
def rhoDropConstructor :
    StructuralMorphism.AuthoredConstructor rhoValidatedLanguageDef :=
  ⟨rhoCalc.terms[1], List.getElem_mem (by simp [rhoCalc])⟩

/-- Drop belongs to the wrapped rho fragment. -/
theorem rhoDrop_mem_wrappedConstructors :
    rhoDropConstructor ∈
      rhoCIGSLT.continuationRetyping.wrappedConstructors :=
  (rhoCIGSLT.continuationRetyping.mem_wrappedConstructors_iff
    rhoDropConstructor).2 (by
      constructor
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide)
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide))

/-- The declared Cost constructor presenting Drop at a selected colour. -/
def rhoDropDeclared : CostStaticColor → rhoCIGSLT.DeclaredCostConstructor
  | .base => ⟨.base rhoDropConstructor, True.intro⟩
  | .wrapped => ⟨.wrapped rhoDropConstructor, rhoDrop_mem_wrappedConstructors⟩

theorem rhoDropDeclared_role (color : CostStaticColor) :
    rhoCIGSLT.declaredCostConstructorRole (rhoDropDeclared color) =
      .static color := by
  cases color <;> rfl

theorem rhoDropDeclared_render (color : CostStaticColor) :
    rhoCIGSLT.renderDeclaredCostConstructor (rhoDropDeclared color) =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).dropConstructor := by
  cases color <;> rfl

/-- Only the selected colour's declared Drop renders to its generated Drop
wire name. -/
theorem rhoRole_static_of_render_eq_drop {color : CostStaticColor}
    (constructor : rhoCIGSLT.DeclaredCostConstructor)
    (rendered : rhoCIGSLT.renderDeclaredCostConstructor constructor =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).dropConstructor) :
    rhoCIGSLT.declaredCostConstructorRole constructor = .static color := by
  have equality : constructor = rhoDropDeclared color :=
    rhoCIGSLT.renderDeclaredCostConstructor_injective
      (rendered.trans (rhoDropDeclared_render color).symm)
  rw [equality, rhoDropDeclared_role]

/-- Reindex an argument plan along equality of its authored parameter spine. -/
def reindexCostStaticArgumentPlanParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam}
    (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    CostStaticArgumentPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer wireName before arguments first := by
  cases equal
  exact plan

@[simp] theorem abstractPatterns_reindexCostStaticArgumentPlanParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam} (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    (reindexCostStaticArgumentPlanParameters equal plan).abstractPatterns =
      plan.abstractPatterns := by
  cases equal
  rfl

@[simp] theorem boundaryTableEntries_reindexCostStaticArgumentPlanParameters
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {wireName : String} {before arguments : List Pattern}
    {first second : List TermParam} (equal : first = second)
    (plan : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName before arguments
      second) :
    (reindexCostStaticArgumentPlanParameters equal plan).boundaryTable.entries =
      plan.boundaryTable.entries := by
  cases equal
  rfl

/-- Reindexing a plan's pattern and source-type fibres preserves admission. -/
theorem rawAdmission_reindexCostStaticRegionPlanPatternSourceType
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {firstPattern secondPattern : Pattern} {firstType secondType : TypeExpr}
    (patternEq : firstPattern = secondPattern)
    (typeEq : firstType = secondType)
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer firstPattern firstType)
    (admission : plan.RawAdmission) :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      patternEq typeEq plan).RawAdmission := by
  cases patternEq
  cases typeEq
  exact admission

/-- Every related left member of a pointwise list relation has a related
right member. -/
theorem exists_right_of_forall₂_mem_left
    {Left Right : Type*} {relation : Left → Right → Prop}
    {left : List Left} {right : List Right}
    (aligned : List.Forall₂ relation left right)
    {item : Left} (membership : item ∈ left) :
    ∃ target ∈ right, relation item target := by
  induction aligned with
  | nil => cases membership
  | @cons source target left right head tail inductionHypothesis =>
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨target, by simp, head⟩
      · obtain ⟨target', targetMembership, related⟩ :=
          inductionHypothesis membership
        exact ⟨target', by simp [targetMembership], related⟩

/-- A unary simple-parameter spine exposes its unique child plan together
with the exact embedding of the child's boundary table. -/
theorem CostStaticArgumentPlan.exists_singletonSimpleChild
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {wireName parameterName : String} {arguments : List Pattern}
    {expected : TypeExpr}
    (spine : CostStaticArgumentPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer wireName [] arguments
      [.simple parameterName expected]) :
    ∃ argument,
      ∃ head : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable
        (outer.comp (.apply wireName [] .hole [])) argument expected,
        arguments = [argument] ∧
        spine.abstractPatterns = [head.abstractPattern] ∧
        Nonempty (CostStaticPlanEntryEmbedding source color targetFree
          head.boundaryTable.entries spine.boundaryTable.entries) := by
  cases spine with
  | @cons _ _ _ _ _ _ _ argument arguments parameter parameters
      sourceExpected representation parameterType head tail =>
      cases tail
      have sourceExpectedEq : sourceExpected = expected := by
        exact (Option.some.inj parameterType).symm
      subst sourceExpected
      refine ⟨argument, head, rfl, rfl, ?_⟩
      refine ⟨?_⟩
      change CostStaticPlanEntryEmbedding source color targetFree
        head.boundaryTable.entries
        (TypedCostRegionBoundaryTable.append head.boundaryTable
          (CostStaticArgumentPlan.nil).boundaryTable).entries
      rw [TypedCostRegionBoundaryTable.entries_append]
      exact CostStaticPlanEntryEmbedding.appendLeft _ _

/-- A reached authored Quote retains its unique process-typed argument plan at
the quote-sealed availability. -/
theorem CostStaticPlanReached.exists_quoteArgumentPlan
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor) :
    ∃ inner innerAbstract,
      payload = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor [inner] ∧
      reached.plan.abstractPattern = .apply
          rhoReflectivePresentation.quoteConstructor [innerAbstract] ∧
      ∃ child : CostStaticPlanReached rhoCIGSLT color targetFree inner
          (.apply rhoReflectivePresentation.quoteConstructor [innerAbstract]),
        child.sourceBound = reached.sourceBound ∧
        child.targetBound = reached.targetBound ∧
        HEq child.thinning reached.thinning ∧
        child.sourceAvailable = [] ∧
        child.sourceType = .base "Proc" ∧
        child.plan.abstractPattern = innerAbstract ∧
        child.plan.RawAdmission ∧
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          child.plan.boundaryTable.entries
          reached.plan.boundaryTable.entries) := by
  obtain ⟨sourceBound, targetBound, thinning, sourceAvailable, outer,
      sourceType, plan, skeletonContext, abstractEq⟩ := reached
  change plan.RawAdmission at admission
  change plan.rootClass =
    .application rhoReflectivePresentation.quoteConstructor at quoteRoot
  cases plan with
  | application constructor rendered current preimage notBare children =>
      rename_i wireName arguments
      have sourceLabel : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using
          CostStaticPlanRootClass.application.inj quoteRoot
      have generatedLabel : wireName =
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor := by
        calc
          wireName = rhoCIGSLT.renderDeclaredCostConstructor constructor :=
            rendered.symm
          _ = (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label :=
            (rhoCIGSLT.materializeDeclaredCostConstructor_label constructor).symm
          _ = (color.symbols rhoCIGSLT).constructor
              preimage.sourceConstructor.1.label := preimage.labelMap
          _ = (color.symbols rhoCIGSLT).constructor
              rhoReflectivePresentation.quoteConstructor := by rw [sourceLabel]
          _ = (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).quoteConstructor := by
            cases color <;> rfl
      have paramsShape : preimage.sourceConstructor.1.params =
          [.simple "p" (.base "Proc")] := by
        exact rhoCalc_params_eq_singleton_process_of_label_eq_quote
          preimage.sourceConstructor sourceLabel
      have quoteDetected :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
              preimage.sourceConstructor.1.label = true := by
        rw [sourceLabel]
        simpa [LanguageDefContinuedInteraction.rhoCIGSLT, rhoIGSLT,
          rhoInteractivePresentation, rhoValidatedLanguageDef,
          rhoReflectivePresentation] using rho_isQuoteConstructor_quote
      let quoteChildren : CostStaticArgumentPlan rhoCIGSLT color targetFree
          sourceBound targetBound thinning
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true
            then [] else sourceAvailable)
          outer wireName [] arguments [.simple "p" (.base "Proc")] :=
        reindexCostStaticArgumentPlanParameters paramsShape.symm children
      obtain ⟨argument, head, argumentsShape, abstractShape,
          childEmbedding⟩ :=
        CostStaticArgumentPlan.exists_singletonSimpleChild quoteChildren
      have payloadShape :
          Pattern.apply wireName arguments =
            .apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation).quoteConstructor [argument] := by
        rw [argumentsShape, generatedLabel]
      let child : CostStaticPlanReached rhoCIGSLT color targetFree argument
          (.apply rhoReflectivePresentation.quoteConstructor
            [head.abstractPattern]) :=
        { sourceBound := sourceBound
          targetBound := targetBound
          thinning := thinning
          sourceAvailable := _
          outer := _
          sourceType := .base "Proc"
          plan := head
          skeletonContext :=
            .apply rhoReflectivePresentation.quoteConstructor [] .hole []
          abstract_eq := by rfl }
      have materializedMembership :
          rhoCIGSLT.materializeDeclaredCostConstructor constructor ∈
            rhoCIGSLT.costWholeLanguage.terms := by
        simpa only [rhoCIGSLT.costWholeLanguage_terms] using
          rhoCIGSLT.materializeDeclaredCostConstructor_mem constructor
      obtain ⟨targetRule, targetMembership, targetLabel, _targetNotBare,
          _targetType, argumentsTypedAtParent⟩ :=
        hasType_apply_inversion admission.wellSorted.1.1
      have targetRuleEq : targetRule =
          rhoCIGSLT.materializeDeclaredCostConstructor constructor :=
        rhoCIGSLT.costWholeLanguage_labelDeterministic targetMembership
          materializedMembership
          (targetLabel.symm.trans
            ((rhoCIGSLT.materializeDeclaredCostConstructor_label constructor).trans
              rendered).symm)
      subst targetRule
      have generatedQuoteMarked :
          ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.costWholeReflectionProfile
              (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label =
            true := by
        rw [rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered,
          generatedLabel]
        apply isQuoteConstructor_costStaticReflectivePresentationDecl
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile]
      have argumentsScopedZero :
          Pattern.isWellScopedListAt 0 arguments = true :=
        WellSorted.isWellScopedListAt_zero_of_typed_quote
          rhoCIGSLT.costWholeLanguage_validate
          rhoCIGSLT.costWholeReflectionProfile_validate
          materializedMembership argumentsTypedAtParent generatedQuoteMarked
          (by
            simpa only [rhoCIGSLT.materializeDeclaredCostConstructor_label,
              rendered] using admission.wellSorted.2)
      have argumentsTypedAtZero : ArgumentsHaveTypes
          rhoCIGSLT.costWholeLanguage targetFree [] arguments
          (rhoCIGSLT.materializeDeclaredCostConstructor constructor).params := by
        simpa using argumentsTypedAtParent.restrictOuterOfScoped
          (inner := []) (outer := sourceAvailable) argumentsScopedZero
      rw [preimage.parametersMap, paramsShape, argumentsShape] at argumentsTypedAtZero
      cases argumentsTypedAtZero with
      | @cons _ _ _ parameter parameters expected representation
          parameterType argumentTyped tailTyped =>
        cases tailTyped
        have expectedMappedProcess : expected =
            mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") := by
          simpa [mapTermParam] using (Option.some.inj parameterType).symm
        subst expected
        have argumentCanonical :
            Pattern.hasCanonicalBinderMetadata argument = true := by
          have parentCanonical := admission.wellSorted.1.2.1
          rw [argumentsShape] at parentCanonical
          simpa [Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList] using parentCanonical
        have argumentObject : isObjectPattern argument = true := by
          have parentObject := admission.wellSorted.1.2.2.1
          simpa [isObjectPattern, isObjectPatternList, argumentsShape] using
            parentObject
        have argumentScoped : argument.isWellScopedAt 0 = true := by
          simpa [Pattern.isWellScopedListAt, argumentsShape] using
            argumentsScopedZero
        have argumentsReflective :
            ∀ presentation ∈ rhoCIGSLT.costWholeReflectionProfile.presentations,
              binderSafeListAt presentation.quoteConstructor 0 arguments =
                true :=
          WellSorted.reflectiveScopeSafeListAt_zero_of_typed_quote
            rhoCIGSLT.costWholeLanguage_validate
            rhoCIGSLT.costWholeReflectionProfile_validate
            materializedMembership argumentsTypedAtParent generatedQuoteMarked
            (by
              simpa only [rhoCIGSLT.materializeDeclaredCostConstructor_label,
                rendered] using admission.wellSorted.2)
        have argumentReflective :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              rhoCIGSLT.costWholeReflectionProfile 0 argument := by
          intro presentation presentationMembership
          have safe := argumentsReflective presentation presentationMembership
          rw [argumentsShape] at safe
          simpa [binderSafeListAt] using safe
        have childAdmission : child.plan.RawAdmission := by
          change head.RawAdmission
          refine ⟨?_, ?_⟩
          · simpa [quoteDetected] using
              (show ReflectiveWellSorted.OpenPatternWellSorted
                rhoCIGSLT.costWholeReflectionProfile
                rhoCIGSLT.costWholeLanguage targetFree []
                (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc"))
                argument from
                  ⟨⟨argumentTyped, argumentCanonical, argumentObject,
                    argumentScoped⟩, argumentReflective⟩)
          · refine ⟨targetBound, ?_⟩
            simp [quoteDetected]
        refine ⟨argument, head.abstractPattern, payloadShape, ?_, child,
          rfl, rfl, HEq.rfl, ?_, rfl, rfl, childAdmission, ?_⟩
        · have originalAbstractShape : children.abstractPatterns =
              [head.abstractPattern] := by
            rw [← abstractPatterns_reindexCostStaticArgumentPlanParameters
              paramsShape.symm children]
            exact abstractShape
          change Pattern.apply preimage.sourceConstructor.1.label
            children.abstractPatterns =
              Pattern.apply rhoReflectivePresentation.quoteConstructor
                [head.abstractPattern]
          rw [originalAbstractShape]
          exact congrArg
            (fun label => Pattern.apply label [head.abstractPattern]) sourceLabel
        · exact (if_pos quoteDetected)
        · change Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
            targetFree head.boundaryTable.entries
              children.boundaryTable.entries)
          obtain ⟨embedding⟩ := childEmbedding
          have entriesEq :=
            boundaryTableEntries_reindexCostStaticArgumentPlanParameters
              paramsShape.symm children
          rw [entriesEq] at embedding
          exact ⟨embedding⟩
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- Extend an enclosing canonical type route through the unique process
parameter of an authored rho Quote plan. -/
def CostStaticPlanReached.quoteArgumentRoute
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    {rootType : TypeExpr}
    (route : CostCanonicalTypeRoute rhoCIGSLT color rootType
      (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType)) :
    CostCanonicalTypeRoute rhoCIGSLT color rootType
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
  obtain ⟨sourceBound, targetBound, thinning, sourceAvailable, outer,
      sourceType, plan, skeletonContext, abstractEq⟩ := reached
  change plan.rootClass = .application
    rhoReflectivePresentation.quoteConstructor at quoteRoot
  change CostCanonicalTypeRoute rhoCIGSLT color rootType
    (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) at route
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have sourceLabel : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor := by
        simpa [CostStaticRegionPlan.rootClass] using
          CostStaticPlanRootClass.application.inj quoteRoot
      have paramsShape : preimage.sourceConstructor.1.params =
          [.simple "p" (.base "Proc")] :=
        rhoCalc_params_eq_singleton_process_of_label_eq_quote
          preimage.sourceConstructor sourceLabel
      have prior : CostCanonicalTypeRoute rhoCIGSLT color rootType
          (.base
            (rhoCIGSLT.materializeDeclaredCostConstructor constructor
              ).category) :=
        route.castEndpoint (by
          simpa [mapTypeExpr] using congrArg TypeExpr.base
            preimage.categoryMap.symm)
      apply CostCanonicalTypeRoute.parameter
        (parameter := mapTermParam (color.symbols rhoCIGSLT)
          (.simple "p" (.base "Proc"))) prior
      · simpa only [rhoCIGSLT.costWholeLanguage_terms] using
          rhoCIGSLT.materializeDeclaredCostConstructor_mem constructor
      · intro targetBare
        exact notBare (preimage.source_usesBareCollection current targetBare)
      · rw [preimage.parametersMap]
        apply List.mem_map_of_mem
        rw [paramsShape]
        simp
      · rfl
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at quoteRoot

/-- A reached current-colour Drop retains its unique name-typed argument plan
at the same availability, together with admission and boundary-table
provenance. -/
theorem CostStaticPlanReached.exists_dropArgumentPlan
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rawName rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [rawName])
      rootAbstract)
    (admission : reached.plan.RawAdmission) :
    ∃ nameAbstract,
      reached.plan.abstractPattern =
        .apply rhoReflectivePresentation.dropConstructor [nameAbstract] ∧
      ∃ child : CostStaticPlanReached rhoCIGSLT color targetFree rawName
          (.apply rhoReflectivePresentation.dropConstructor [nameAbstract]),
        child.sourceBound = reached.sourceBound ∧
        child.targetBound = reached.targetBound ∧
        HEq child.thinning reached.thinning ∧
        child.sourceAvailable = reached.sourceAvailable ∧
        child.sourceType = .base "Name" ∧
        child.plan.abstractPattern = nameAbstract ∧
        child.plan.RawAdmission ∧
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          child.plan.boundaryTable.entries
          reached.plan.boundaryTable.entries) := by
  obtain ⟨sourceBound, targetBound, thinning, sourceAvailable, outer,
      sourceType, plan, skeletonContext, abstractEq⟩ := reached
  change plan.RawAdmission at admission
  cases plan with
  | application constructor rendered current preimage notBare children =>
      have sourceLabel : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.dropConstructor := by
        apply CostStaticColor.symbols_constructor_injective rhoCIGSLT color
        rw [← preimage.labelMap,
          rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered]
        cases color <;> rfl
      have paramsShape : preimage.sourceConstructor.1.params =
          [.simple "n" (.base "Name")] :=
        rhoCalc_params_eq_singleton_name_of_label_eq_drop
          preimage.sourceConstructor sourceLabel
      have sourceDropOrdinary :
          ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1
              preimage.sourceConstructor.1.label = false := by
        rw [sourceLabel]
        decide
      let dropChildren : CostStaticArgumentPlan rhoCIGSLT color targetFree
          sourceBound targetBound thinning
          (if ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.reflection.1 preimage.sourceConstructor.1.label = true
            then [] else sourceAvailable)
          outer
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).dropConstructor
            [] [rawName] [.simple "n" (.base "Name")] :=
        reindexCostStaticArgumentPlanParameters paramsShape.symm children
      obtain ⟨argument, head, argumentShape, abstractShape,
          ⟨headEmbedding⟩⟩ :=
        CostStaticArgumentPlan.exists_singletonSimpleChild dropChildren
      have argumentEq : argument = rawName := by
        simpa using (congrArg List.head? argumentShape).symm
      subst argument
      let child : CostStaticPlanReached rhoCIGSLT color targetFree rawName
          (.apply rhoReflectivePresentation.dropConstructor
            [head.abstractPattern]) :=
        { sourceBound := sourceBound
          targetBound := targetBound
          thinning := thinning
          sourceAvailable := _
          outer := _
          sourceType := .base "Name"
          plan := head
          skeletonContext :=
            .apply rhoReflectivePresentation.dropConstructor [] .hole []
          abstract_eq := by rfl }
      have materializedMembership :
          rhoCIGSLT.materializeDeclaredCostConstructor constructor ∈
            rhoCIGSLT.costWholeLanguage.terms := by
        simpa only [rhoCIGSLT.costWholeLanguage_terms] using
          rhoCIGSLT.materializeDeclaredCostConstructor_mem constructor
      obtain ⟨targetRule, targetMembership, targetLabel, _targetNotBare,
          _targetType, argumentsTyped⟩ :=
        hasType_apply_inversion admission.wellSorted.1.1
      have targetRuleEq : targetRule =
          rhoCIGSLT.materializeDeclaredCostConstructor constructor :=
        rhoCIGSLT.costWholeLanguage_labelDeterministic targetMembership
          materializedMembership
          (targetLabel.symm.trans
            ((rhoCIGSLT.materializeDeclaredCostConstructor_label constructor).trans
              rendered).symm)
      subst targetRule
      rw [preimage.parametersMap, paramsShape] at argumentsTyped
      cases argumentsTyped with
      | @cons _ _ _ parameter parameters expected representation
          parameterType argumentTyped tailTyped =>
        cases tailTyped
        have expectedMappedName : expected =
            mapTypeExpr (color.symbols rhoCIGSLT) (.base "Name") := by
          simpa [mapTermParam] using (Option.some.inj parameterType).symm
        subst expected
        have argumentCanonical :
            Pattern.hasCanonicalBinderMetadata rawName = true := by
          have parentCanonical := admission.wellSorted.1.2.1
          simpa [Pattern.hasCanonicalBinderMetadata,
            Pattern.hasCanonicalBinderMetadataList] using parentCanonical
        have argumentObject : isObjectPattern rawName = true := by
          have parentObject := admission.wellSorted.1.2.2.1
          simpa [isObjectPattern, isObjectPatternList] using parentObject
        have targetDropOrdinary :
            ReflectiveContextSupport.isQuoteConstructor
              rhoCIGSLT.costWholeReflectionProfile
              (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label =
                false := by
          rw [rhoCIGSLT.materializeDeclaredCostConstructor_label, rendered]
          exact CostCanonicalLaws.rho_costStatic_drop_isOrdinary color
        have parentReflective :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
              (.apply
                (rhoCIGSLT.materializeDeclaredCostConstructor constructor).label
                [rawName]) := by
          simpa only [rhoCIGSLT.materializeDeclaredCostConstructor_label,
            rendered] using admission.wellSorted.2
        have argumentsReflective :=
          WellSorted.reflectiveScopeSafeListAt_of_nonquote
            targetDropOrdinary parentReflective
        have argumentReflective :
            ReflectiveWellSorted.ReflectiveScopeSafeAt
              rhoCIGSLT.costWholeReflectionProfile sourceAvailable.length
              rawName := by
          intro presentation presentationMembership
          have safe := argumentsReflective presentation presentationMembership
          simpa [binderSafeListAt] using safe
        have childAdmission : child.plan.RawAdmission := by
          change head.RawAdmission
          refine ⟨?_, ?_⟩
          · simpa [sourceDropOrdinary] using
              (show ReflectiveWellSorted.OpenPatternWellSorted
                rhoCIGSLT.costWholeReflectionProfile
                rhoCIGSLT.costWholeLanguage targetFree sourceAvailable
                (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Name")) rawName
                from ⟨⟨argumentTyped, argumentCanonical, argumentObject,
                  argumentTyped.isWellScopedAt⟩, argumentReflective⟩)
          · simpa [sourceDropOrdinary] using admission.targetBound_split
        refine ⟨head.abstractPattern, ?_, child, rfl, rfl, HEq.rfl, ?_,
          rfl, rfl, childAdmission, ?_⟩
        · have originalAbstractShape : children.abstractPatterns =
              [head.abstractPattern] := by
            rw [← abstractPatterns_reindexCostStaticArgumentPlanParameters
              paramsShape.symm children]
            exact abstractShape
          change Pattern.apply preimage.sourceConstructor.1.label
            children.abstractPatterns =
              Pattern.apply rhoReflectivePresentation.dropConstructor
                [head.abstractPattern]
          rw [originalAbstractShape]
          exact congrArg
            (fun label => Pattern.apply label [head.abstractPattern]) sourceLabel
        · simp [child, sourceDropOrdinary]
        · change Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
            targetFree head.boundaryTable.entries
              children.boundaryTable.entries)
          have entriesEq :=
            boundaryTableEntries_reindexCostStaticArgumentPlanParameters
              paramsShape.symm children
          rw [entriesEq] at headEmbedding
          exact ⟨headEmbedding⟩
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      exact (outsideCurrent
        (rhoRole_static_of_render_eq_drop constructor rendered)).elim

/-- If the unique process argument of a reached Quote canonically exposes a
Drop, the exact raw Drop leaf has a reached admitted plan embedded in the
Quote plan. -/
theorem CostStaticPlanReached.exists_reachedDropLeaf_of_quoteCanonicalDrop
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract inner name : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (payloadShape : payload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [inner])
    (canonicalInner : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) inner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [name]) :
    ∃ innerAbstract rawName rawAbstract,
      reached.plan.abstractPattern =
        .apply rhoReflectivePresentation.quoteConstructor [innerAbstract] ∧
      RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
          innerAbstract =
        [rawAbstract] ∧
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) rawName = name ∧
      sizeOf rawName < sizeOf payload ∧
      ∃ rawReached : CostStaticPlanReached rhoCIGSLT color targetFree
          (.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).dropConstructor [rawName])
          innerAbstract,
        rawReached.sourceBound = reached.sourceBound ∧
        rawReached.targetBound = reached.targetBound ∧
        HEq rawReached.thinning reached.thinning ∧
        rawReached.sourceAvailable = [] ∧
        rawReached.sourceType = .base "Proc" ∧
        rawReached.plan.abstractPattern = rawAbstract ∧
        rawReached.plan.RawAdmission ∧
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          rawReached.plan.boundaryTable.entries
          reached.plan.boundaryTable.entries) := by
  obtain ⟨argument, innerAbstract, reachedPayloadShape, abstractShape,
      child, childSourceBound, childTargetBound, childThinning,
      childAvailable, childProcess, childAbstract, childAdmission,
      ⟨childEmbedding⟩⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_quoteArgumentPlan
      reached admission quoteRoot
  have argumentEq : argument = inner := by
    rw [payloadShape] at reachedPayloadShape
    injection reachedPayloadShape with _ argumentsEq
    exact (List.cons.inj argumentsEq).1.symm
  subst argument
  let childProcessPlan :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.reindexPatternSourceType
      rfl childProcess child.plan
  have childProcessAdmission : childProcessPlan.RawAdmission := by
    exact rawAdmission_reindexCostStaticRegionPlanPatternSourceType rfl
      childProcess child.plan childAdmission
  have childProcessAbstract : childProcessPlan.abstractPattern =
      innerAbstract := by
    exact (CostStaticRegionPlan.reindexPatternSourceType_abstractPattern
      rfl childProcess child.plan).trans childAbstract
  have childTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      child.sourceAvailable inner
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).processSort) := by
    have typed := childProcessAdmission.wellSorted.1.1
    simpa [costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation,
      rhoReflectivePresentation, mapTypeExpr] using typed
  have childObject : isObjectPattern inner = true := childAdmission.object
  obtain ⟨rawName, leaves, _rawTyped, _rawObject, rawCanonical⟩ :=
    RhoCommonRestorationApex.rhoProc_canonical_drop_leaf_exposure
      (fun _ _ => (0 : Nat)) color childTyped childObject canonicalInner 0
  have traversal :=
    ParallelFrontier.parallelLeaves_abstractPattern_forall2 childProcessPlan
      childProcessAdmission
  have rawMembership : .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).dropConstructor [rawName] ∈
      RhoCommonRestorationApex.parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) inner := by
    rw [leaves]
    simp
  have rawDropBound := ParallelFrontier.sizeOf_le_of_mem_parallelLeaves
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation)
    inner
    (.apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).dropConstructor [rawName]) rawMembership
  have rawNameSmaller : sizeOf rawName < sizeOf payload := by
    have nameBelowDrop : sizeOf rawName < sizeOf (Pattern.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [rawName]) := by
      simp_wf
      omega
    have nameBelowInner : sizeOf rawName < sizeOf inner :=
      lt_of_lt_of_le nameBelowDrop rawDropBound
    rw [payloadShape]
    simp_wf
    omega
  obtain ⟨abstractLeaf, abstractMembership, leafWitness⟩ :=
    exists_right_of_forall₂_mem_left traversal rawMembership
  have abstractLeaves :
      RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
          innerAbstract =
        [abstractLeaf] := by
    have lengths := List.Forall₂.length_eq traversal
    rw [leaves] at lengths
    rw [childProcessAbstract] at lengths abstractMembership
    have abstractLength :
        (RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
          innerAbstract).length = 1 := by
      simpa using lengths.symm
    obtain ⟨only, shape⟩ := List.length_eq_one_iff.mp abstractLength
    rw [shape] at abstractMembership
    have onlyEq : only = abstractLeaf := by
      exact (by simpa using abstractMembership : abstractLeaf = only).symm
    subst only
    exact shape
  obtain ⟨rawReached, rawSourceBound, rawTargetBound, rawThinning,
      rawAvailable, rawProcess, rawAbstract, rawAdmission,
      ⟨rawEmbedding⟩⟩ :=
    ParallelFrontier.LeafWitness.exists_reached leafWitness
  let rawReachedAtArgument : CostStaticPlanReached rhoCIGSLT color targetFree
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [rawName])
      innerAbstract :=
    rawReached.rebaseAbstractRoot .hole (by
      simpa using childProcessAbstract.symm)
  have processEntriesEq : childProcessPlan.boundaryTable.entries =
      child.plan.boundaryTable.entries :=
    CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries
      rfl childProcess child.plan
  rw [processEntriesEq] at rawEmbedding
  refine ⟨innerAbstract, rawName, abstractLeaf, abstractShape,
    abstractLeaves, rawCanonical, rawNameSmaller, rawReachedAtArgument, ?_, ?_,
    ?_, ?_, rawProcess, rawAbstract, rawAdmission,
    ⟨rawEmbedding.comp childEmbedding⟩⟩
  · exact rawSourceBound.trans childSourceBound
  · exact rawTargetBound.trans childTargetBound
  · exact rawThinning.trans childThinning
  · exact rawAvailable.trans childAvailable

/-- A reached Quote whose process argument canonically exposes a Drop retains
the Drop's exact raw Name child as a sealed reached plan, embedded all the way
back into the Quote plan. -/
theorem CostStaticPlanReached.exists_reachedName_of_quoteCanonicalDrop
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract inner name : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (payloadShape : payload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [inner])
    (canonicalInner : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) inner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [name]) :
    ∃ innerAbstract rawName rawDropAbstract nameAbstract,
      reached.plan.abstractPattern =
        .apply rhoReflectivePresentation.quoteConstructor [innerAbstract] ∧
      RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
          innerAbstract = [rawDropAbstract] ∧
      rawDropAbstract =
        .apply rhoReflectivePresentation.dropConstructor [nameAbstract] ∧
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) rawName = name ∧
      sizeOf rawName < sizeOf payload ∧
      ∃ nameReached : CostStaticPlanReached rhoCIGSLT color targetFree
          rawName rootAbstract,
        nameReached.sourceBound = reached.sourceBound ∧
        nameReached.targetBound = reached.targetBound ∧
        HEq nameReached.thinning reached.thinning ∧
        nameReached.sourceAvailable = [] ∧
        nameReached.sourceType = .base "Name" ∧
        nameReached.plan.abstractPattern = nameAbstract ∧
        nameReached.plan.RawAdmission ∧
        Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          nameReached.plan.boundaryTable.entries
          reached.plan.boundaryTable.entries) := by
  obtain ⟨innerAbstract, rawName, rawDropAbstract, outerShape,
      abstractLeaves, rawCanonical, rawNameSmaller, rawReached, rawSourceBound,
      rawTargetBound, rawThinning, rawAvailable, _rawProcess,
      rawAbstract, rawAdmission, ⟨rawEmbedding⟩⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_reachedDropLeaf_of_quoteCanonicalDrop
      reached admission quoteRoot payloadShape canonicalInner
  obtain ⟨nameAbstract, rawDropShape, nameChild, nameSourceBound,
      nameTargetBound, nameThinning, nameAvailable, nameType, nameAbstractEq,
      nameAdmission, ⟨nameEmbedding⟩⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_dropArgumentPlan
      rawReached rawAdmission
  have rawDropAbstractShape : rawDropAbstract =
      .apply rhoReflectivePresentation.dropConstructor [nameAbstract] :=
    rawAbstract.symm.trans rawDropShape
  let nameAtInner := nameChild.rebaseAbstractRoot rawReached.skeletonContext
    (by
      calc
        innerAbstract = rawReached.skeletonContext.fill
            rawReached.plan.abstractPattern := rawReached.abstract_eq
        _ = rawReached.skeletonContext.fill
            (.apply rhoReflectivePresentation.dropConstructor [nameAbstract]) :=
          congrArg rawReached.skeletonContext.fill rawDropShape)
  let quoteFrame :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext :=
    .apply rhoReflectivePresentation.quoteConstructor [] .hole []
  let nameAtRoot := nameAtInner.rebaseAbstractRoot quoteFrame (by
    change reached.plan.abstractPattern =
      .apply rhoReflectivePresentation.quoteConstructor [innerAbstract]
    exact outerShape)
  let nameAtParent := nameAtRoot.rebaseAbstractRoot reached.skeletonContext
    reached.abstract_eq
  refine ⟨innerAbstract, rawName, rawDropAbstract, nameAbstract, outerShape,
    abstractLeaves, rawDropAbstractShape, rawCanonical, rawNameSmaller,
    nameAtParent, ?_, ?_, ?_, ?_, ?_, ?_, nameAdmission, ?_⟩
  · exact nameSourceBound.trans rawSourceBound
  · exact nameTargetBound.trans rawTargetBound
  · exact nameThinning.trans rawThinning
  · exact nameAvailable.trans rawAvailable
  · exact nameType
  · exact nameAbstractEq
  · exact ⟨nameEmbedding.comp rawEmbedding⟩

/-- Two reached authored Quotes have a parent-cospan apex whenever executable
payload trees in their exact availability fibres have the same hereditary
normal form. -/
noncomputable def quotePlanStops_commonRestorationApex_of_payloadNormalEq
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (leftTree : CostRegionTree rhoCIGSLT targetFree
      leftReached.sourceAvailable [] leftPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType))
    (rightTree : CostRegionTree rhoCIGSLT targetFree
      rightReached.sourceAvailable [] rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (payloadNormalEq :
      (leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftFrame := leftView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
          leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftReached.plan.abstractPattern)))
  let rightFrame := rightView.node.thinning.thickenAmbientBVars callbackScope
    (mapPattern (color.symbols rhoCIGSLT)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
          rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightReached.plan.abstractPattern)))
  have leftCovered : leftEnvironment.Covers leftFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        leftView.node leftEnvironment leftReached callbackAvailable
          callbackScope
  have rightCovered : rightEnvironment.Covers rightFrame := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_atomCovered
        rightView.node rightEnvironment rightReached callbackAvailable
          callbackScope
  have leftRestore : ∀ restorationDepth,
      leftEnvironment.restoreAt restorationDepth leftFrame =
        (leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        leftView.node leftView.children leftEnvironment leftReached
          leftAdmission leftQuote leftEmbedding leftTree callbackAvailable
            callbackScope restorationDepth
  have rightRestore : ∀ restorationDepth,
      rightEnvironment.restoreAt restorationDepth rightFrame =
        (rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    intro restorationDepth
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
        rightView.node rightView.children rightEnvironment rightReached
          rightAdmission rightQuote rightEmbedding rightTree callbackAvailable
            callbackScope restorationDepth
  subst leftAbstractEq
  subst rightAbstractEq
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro restorationDepth
  have leftFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
      restorationDepth leftFrame leftCovered
  have rightFactor :=
    CostStaticAtomEnvironment.substituteAt_reifyAtomsWith_eq_restoreAt
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
      restorationDepth rightFrame rightCovered
  have endpointEq : leftEnvironment.restoreAt restorationDepth leftFrame =
      rightEnvironment.restoreAt restorationDepth rightFrame :=
    (leftRestore restorationDepth).trans
      (payloadNormalEq.trans (rightRestore restorationDepth).symm)
  exact leftFactor.trans (endpointEq.trans rightFactor.symm)

/-- Paired reached Quotes close recursively whenever their exact availability
fibres agree or either endpoint is sealed. -/
noncomputable def quotePlanStops_commonRestorationApex_of_closeSmaller_supportCase
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (supportCase :
      leftReached.sourceAvailable = rightReached.sourceAvailable ∨
      leftReached.sourceAvailable = [] ∨
      rightReached.sourceAvailable = [])
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  rcases supportCase with supportEq | leftSealed | rightSealed
  · have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree leftReached.sourceAvailable
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
        rightPayload := by
      rw [supportEq, sourceTypeEq]
      exact rightAdmission.wellSorted
    have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
      rw [sourceTypeEq]
      exact rightAdmissible
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAdmission.wellSorted rightWellSorted
        canonical smaller leftAdmissible)
    let rightTree : CostRegionTree rhoCIGSLT targetFree
        rightReached.sourceAvailable [] rightPayload
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
      CostRegionTree.reindexFiber supportEq rfl
        (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq)
          pair.rightTree
    have pairNormal :
        (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      have aligned :
          (pair.leftTree.normalize
              (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
            (pair.rightTree.normalize
              (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
        simpa only [rhoHereditaryNormalizationKernel] using
          pair.alignment.normalize_pattern_eq
      exact aligned.trans (by simp [rightTree])
    exact quotePlanStops_commonRestorationApex_of_payloadNormalEq leftView
      rightView leftReached rightReached leftAdmission rightAdmission
      leftAbstractEq rightAbstractEq leftEmbedding rightEmbedding leftQuote
      rightQuote pair.leftTree rightTree pairNormal callbackAvailable
      callbackScope callbackRoot
  · have leftClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree []
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
        leftPayload := by
      simpa only [leftSealed] using leftAdmission.wellSorted
    have leftAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree rightReached.sourceAvailable
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)
        leftPayload := by
      simpa only [sourceTypeEq] using
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          leftClosed rightReached.sourceAvailable
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAtCommon
        rightAdmission.wellSorted canonical smaller rightAdmissible)
    let leftTree := leftReached.payloadTreeOfWellSorted
      leftAdmission.wellSorted
    have leftNormal :
        (leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      exact CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
        (ambient := rightReached.sourceAvailable) (by simp [leftSealed])
          leftTree pair.leftTree rfl
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq)
          leftAdmission.object
    have pairNormal :
        (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      simpa only [rhoHereditaryNormalizationKernel] using
        pair.alignment.normalize_pattern_eq
    exact quotePlanStops_commonRestorationApex_of_payloadNormalEq leftView
      rightView leftReached rightReached leftAdmission rightAdmission
      leftAbstractEq rightAbstractEq leftEmbedding rightEmbedding leftQuote
      rightQuote leftTree pair.rightTree (leftNormal.trans pairNormal)
      callbackAvailable callbackScope callbackRoot
  · have rightClosed : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree []
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)
        rightPayload := by
      simpa only [rightSealed] using rightAdmission.wellSorted
    have rightAtCommon : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree leftReached.sourceAvailable
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
        rightPayload := by
      simpa only [sourceTypeEq] using
        ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
          rightClosed leftReached.sourceAvailable
    have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
      rw [sourceTypeEq]
      exact rightAdmissible
    let pair := Classical.choice
      (closeSmaller (childOuter := []) leftAdmission.wellSorted rightAtCommon
        canonical smaller leftAdmissible)
    let rightTree := rightReached.payloadTreeOfWellSorted
      rightAdmission.wellSorted
    have rightNormal :
        (rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      exact CostStaticRegionNode.CostRegionTree.normalize_pattern_eq_of_availableSuffix
        (ambient := leftReached.sourceAvailable) (by simp [rightSealed])
          rightTree pair.rightTree rfl
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq.symm)
          rightAdmission.object
    have pairNormal :
        (pair.leftTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          (pair.rightTree.normalize
            (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      simpa only [rhoHereditaryNormalizationKernel] using
        pair.alignment.normalize_pattern_eq
    exact quotePlanStops_commonRestorationApex_of_payloadNormalEq leftView
      rightView leftReached rightReached leftAdmission rightAdmission
      leftAbstractEq rightAbstractEq leftEmbedding rightEmbedding leftQuote
      rightQuote pair.leftTree rightTree (pairNormal.trans rightNormal.symm)
      callbackAvailable callbackScope callbackRoot

/-- A reached Quote subplan remains hereditarily typed after reification in
its enclosing semantic environment and transport to the common atom
namespace.  Quote scope-safety makes the enclosing thinning independent of
the callback's structural depth. -/
theorem CostStaticPlanReached.commonReifiedMappedFrame_hereditaryTyped_of_quoteRoot
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries
      parentNode.plan.boundaryTable.entries)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (scopeDepth : Nat) :
    HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext
      (reached.sourceBound.map (mapTypeExpr (color.symbols rhoCIGSLT)))
      (cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify reached.plan.abstractPattern))))
      (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType) := by
  obtain ⟨sourceTyped, _sourceSafe⟩ :=
    reached.plan.abstractPattern_supportedSafe parentNode.finiteBoundaryTable
      embedding.subset
  have abstractObject : isObjectPattern reached.plan.abstractPattern = true :=
    reached.plan.abstractPattern_object admission.object
  have covered : ∀ name,
      name ∈ reached.plan.abstractPattern.freeFvarNames →
      ∃ occurrence : CostStaticFVarOccurrence parentNode.skeleton.1,
        occurrence.name = name := by
    intro name membership
    obtain ⟨localOccurrence, localName⟩ :=
      CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
        membership abstractObject
    let parentOccurrence : CostStaticFVarOccurrence parentNode.skeleton.1 :=
      CostStaticFVarOccurrence.castRoot
        (reached.abstract_eq.symm.trans parentNode.skeleton_pattern.symm)
        (localOccurrence.inContext reached.skeletonContext)
    exact ⟨parentOccurrence, by simp [parentOccurrence, localName]⟩
  have sourceReified := environment.reify_sourceHasTypeWithConstructors
    sourceTyped covered
  have mapped := sourceReified.mapCostStaticHereditary rhoCIGSLT color
  rw [environment.sourceAtomFreeContext_map_eq_atomFreeContext typeMap] at mapped
  have mappedSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT)
        (environment.reify reached.plan.abstractPattern)) = true := by
    have sourceSafe : binderSafeAt rhoReflectivePresentation.quoteConstructor
        0 (environment.reify reached.plan.abstractPattern) = true := by
      rw [CostStaticAtomEnvironment.binderSafeAt_reify]
      exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
        reached.plan quoteRoot
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using sourceSafe
  have thinningEq : parentNode.thinning.thickenAmbientBVars scopeDepth
      (mapPattern (color.symbols rhoCIGSLT)
        (environment.reify reached.plan.abstractPattern)) =
      mapPattern (color.symbols rhoCIGSLT)
        (environment.reify reached.plan.abstractPattern) :=
    parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      scopeDepth _ mappedSafe
  rw [thinningEq]
  have renamed := mapped.renameFVars
    (environment.targetReificationRenaming cospan leg commutes)
  simpa only [CostStaticAtomEnvironment.targetReificationRenaming,
    environment.renameFVars_sourceReificationName_eq_reifyWith] using renamed

/-- The parent-reified frame of any reached generated rho Name is independent
of the keyed canonicalizer's visible depth.  Rigid and boundary roots become
variables; the only generated constructor returning Name is the selected
Quote, whose child depth is reset to zero. -/
theorem CostStaticPlanReached.parentNameFrame_canonicalizeByAt_depth_independent
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (sourceTypeName : reached.sourceType = .base "Name")
    (firstDepth secondDepth scopeDepth : Nat) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let frame := fun pattern =>
      cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (environment.reify pattern)))
    canonicalizeByAt key declaration firstDepth
        (frame reached.plan.abstractPattern) =
      canonicalizeByAt key declaration secondDepth
        (frame reached.plan.abstractPattern) := by
  dsimp only
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (parentNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  have frameApply (constructor : String) (arguments : List Pattern) :
      frame (.apply constructor arguments) =
        .apply ((color.symbols rhoCIGSLT).constructor constructor)
          (arguments.map frame) := by
    dsimp only [frame]
    simp_rw [environment.reify_eq_renameFVars,
      cospan.reifyWith_eq_renameFVars]
    simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
      CostStaticBinderThinning.thickenAmbientBVars, List.map_map]
    rfl
  obtain ⟨sourceBound, targetBound, thinning, sourceAvailable, outer,
      sourceType, plan, skeletonContext, abstractEq⟩ := reached
  change sourceType = .base "Name" at sourceTypeName
  change canonicalizeByAt key declaration firstDepth
      (frame plan.abstractPattern) =
    canonicalizeByAt key declaration secondDepth
      (frame plan.abstractPattern)
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      simp [frame, CostStaticRegionPlan.abstractPattern,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars, canonicalizeByAt]
  | fvar lookup =>
      simp [frame, CostStaticRegionPlan.abstractPattern,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars, canonicalizeByAt]
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      simp [frame, CostStaticRegionPlan.abstractPattern,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars, canonicalizeByAt]
  | application constructor rendered current preimage notBare children =>
      by_cases labelEq : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor
      · rw [CostStaticRegionPlan.abstractPattern, frameApply]
        have mappedQuote :
            (color.symbols rhoCIGSLT).constructor
                preimage.sourceConstructor.1.label =
              declaration.quoteConstructor := by
          simp [labelEq, declaration,
            costStaticReflectivePresentationDecl_eq_map,
            ReflectionExtension.mapReflectivePresentation]
        rw [mappedQuote]
        simp only [canonicalizeByAt, beq_self_eq_true, if_true]
      · have processType := rho_applicationPlan_sourceType_eq_proc_of_not_quote
          (CostStaticRegionPlan.application constructor rendered current
            preimage notBare children) rfl labelEq
        have impossible : (TypeExpr.base "Name") = .base "Proc" :=
          sourceTypeName.symm.trans processType
        have nameEq : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
        contradiction
  | lambda bodyPlan =>
      cases sourceTypeName
  | multiLambda bodyPlan =>
      cases sourceTypeName
  | collection choice selected children =>
      have admissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) := by
        rw [sourceTypeName]
        exact rhoCanonicalRecursiveTypeDomain.base _
      have processType := rho_collectionPlan_sourceType_eq_proc
        (CostStaticRegionPlan.collection choice selected children)
          ⟨_, rfl⟩ admissible
      have impossible : (TypeExpr.base "Name") = .base "Proc" :=
        sourceTypeName.symm.trans processType
      have nameEq : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
      contradiction
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      simp [frame, CostStaticRegionPlan.abstractPattern,
        Pattern.renameFVars, mapPattern,
        CostStaticBinderThinning.thickenAmbientBVars, canonicalizeByAt]

/-- The parent-cospan keyed frame of a Quote whose process argument exposes a
unique Drop is exactly the keyed frame of the surviving reached Name. -/
theorem CostStaticPlanReached.parentCanonicalFrame_eq_nameFrame_of_quoteCanonicalDrop
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.finiteBoundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (typeMap : ∀ slot,
      mapTypeExpr (color.symbols rhoCIGSLT)
          (environment.atomValue slot).key.sourceType =
        (environment.atomValue slot).key.targetType)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount → Fin cospan.commonKeys.length)
    (commutes : ∀ slot,
      cospan.commonKeys.get (leg slot) = (environment.atomValue slot).key)
    {payload rawName innerAbstract rawDropAbstract nameAbstract : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (nameReached : CostStaticPlanReached rhoCIGSLT color targetFree rawName
      parentNode.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries
      parentNode.plan.boundaryTable.entries)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (nameSourceType : nameReached.sourceType = .base "Name")
    (outerShape : reached.plan.abstractPattern =
      .apply rhoReflectivePresentation.quoteConstructor [innerAbstract])
    (abstractLeaves :
      RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
        innerAbstract = [rawDropAbstract])
    (rawDropShape : rawDropAbstract =
      .apply rhoReflectivePresentation.dropConstructor [nameAbstract])
    (nameAbstractEq : nameReached.plan.abstractPattern = nameAbstract)
    (availableDepth scopeDepth : Nat) :
    cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify reached.plan.abstractPattern)))) =
      cospan.reifyWith environment.lookupAtom? leg
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                environment)
              rhoReflectivePresentation availableDepth scopeDepth
              (environment.reify nameReached.plan.abstractPattern)))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let frame := fun pattern =>
    cospan.reifyWith environment.lookupAtom? leg
      (parentNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (environment.reify pattern)))
  have frameApply (constructor : String) (arguments : List Pattern) :
      frame (.apply constructor arguments) =
        .apply ((color.symbols rhoCIGSLT).constructor constructor)
          (arguments.map frame) := by
    dsimp only [frame]
    simp_rw [environment.reify_eq_renameFVars,
      cospan.reifyWith_eq_renameFVars]
    simp only [Pattern.renameFVars, mapPattern, mapPatternList_eq_map,
      CostStaticBinderThinning.thickenAmbientBVars, List.map_map]
    rfl
  have reachedNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify parentNode
      environment cospan leg commutes reached availableDepth scopeDepth
  have nameNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify parentNode
      environment cospan leg commutes nameReached availableDepth scopeDepth
  have rootTyped :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.commonReifiedMappedFrame_hereditaryTyped_of_quoteRoot
      parentNode environment typeMap cospan leg commutes reached admission
        embedding quoteRoot scopeDepth
  have reachedName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    reached.plan quoteRoot
  have rootTypedName : HasTypeWithConstructors rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext
      (reached.sourceBound.map (mapTypeExpr (color.symbols rhoCIGSLT)))
      (frame reached.plan.abstractPattern) (.base declaration.nameSort) := by
    simpa [frame, declaration, reachedName,
      costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation,
      rhoReflectivePresentation, mapTypeExpr] using rootTyped
  have rootFrameShape : frame reached.plan.abstractPattern =
      .apply declaration.quoteConstructor [frame innerAbstract] := by
    rw [outerShape, frameApply]
    simp [declaration, costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation]
  rw [rootFrameShape] at rootTypedName
  have declarationMembership : declaration ∈
      rhoCIGSLT.costWholeReflectionProfile.presentations := by
    simpa [declaration] using
      costStaticReflectivePresentationDecl_mem rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl (by
          change rhoReflectivePresentation.toReflectivePresentationDecl ∈
            ReflectionExtension.rhoReflectionProfile.presentations
          simp [ReflectionExtension.rhoReflectionProfile])
  obtain ⟨argument, argumentTyped, argumentsShape, _argumentSafe⟩ :=
    rootTypedName.toHasType.selectedQuoteArgument
      rhoCIGSLT.costWholeLanguage_validate
      rhoCIGSLT.costWholeReflectionProfile_validate declarationMembership
      (rootTypedName.toHasType.reflectiveSupportSafeAt_empty
        (reached.sourceBound.map
          (mapTypeExpr (color.symbols rhoCIGSLT))))
  have argumentEq : frame innerAbstract = argument := by
    simpa [declaration] using (List.cons.inj argumentsShape).1
  subst argument
  have innerTyped := argumentTyped
  have innerLeaves : RhoCommonRestorationApex.parallelLeaves declaration
      (frame innerAbstract) = [frame rawDropAbstract] := by
    have transported := ParallelFrontier.parallelLeaves_commonReifiedMappedThickened
      environment parentNode.thinning cospan leg rhoReflectivePresentation
        scopeDepth innerAbstract
    change RhoCommonRestorationApex.parallelLeaves declaration
        (frame innerAbstract) =
      (RhoCommonRestorationApex.parallelLeaves rhoReflectivePresentation
        innerAbstract).map frame at transported
    simpa [abstractLeaves] using transported
  have innerKeyed :=
    RhoCommonRestorationApex.rhoProc_canonicalizeByAt_eq_single_parallelLeaf
      key color innerTyped innerLeaves 0
  have rawDropFrameShape : frame rawDropAbstract =
      .apply declaration.dropConstructor [frame nameAbstract] := by
    rw [rawDropShape, frameApply]
    simp [declaration,
      costStaticReflectivePresentationDecl_eq_map,
      ReflectionExtension.mapReflectivePresentation]
  have quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor := by
    simpa [declaration] using (declC_dropNeQuote color).symm
  have dropKeyed : canonicalizeByAt key declaration 0
      (frame rawDropAbstract) =
      .apply declaration.dropConstructor
        [canonicalizeByAt key declaration 0 (frame nameAbstract)] := by
    rw [rawDropFrameShape]
    simp [canonicalizeByAt, canonicalizeListByAt, quoteNeDrop.symm]
  have leftCollapse : canonicalizeByAt key declaration availableDepth
      (frame reached.plan.abstractPattern) =
      canonicalizeByAt key declaration 0 (frame nameAbstract) := by
    rw [rootFrameShape]
    calc
      canonicalizeByAt key declaration availableDepth
          (.apply declaration.quoteConstructor [frame innerAbstract]) =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 (frame innerAbstract)] := by
            simp [canonicalizeByAt, canonicalizeListByAt]
      _ =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalizeByAt key declaration 0 (frame rawDropAbstract)] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) innerKeyed
      _ =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor
            [canonicalizeByAt key declaration 0 (frame nameAbstract)]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) dropKeyed
      _ = canonicalizeByAt key declaration 0 (frame nameAbstract) :=
        finishNormalizeReflectiveApply_quote_drop declaration _
  have nameDepthIndependent : canonicalizeByAt key declaration availableDepth
      (frame nameReached.plan.abstractPattern) =
      canonicalizeByAt key declaration 0
        (frame nameReached.plan.abstractPattern) := by
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentNameFrame_canonicalizeByAt_depth_independent
        parentNode environment cospan leg nameReached nameSourceType
          availableDepth 0 scopeDepth
  have nameAbstractFrame : frame nameReached.plan.abstractPattern =
      frame nameAbstract := congrArg frame nameAbstractEq
  exact reachedNaturality.trans
    (leftCollapse.trans (by
      rw [← nameAbstractFrame]
      exact nameDepthIndependent.symm.trans nameNaturality.symm))

/-- An admitted reached rho Name whose selected-colour canonical form is a
Quote application is itself rooted at the authored Quote constructor. -/
theorem CostStaticPlanReached.rootClass_eq_quote_of_name_canonical_quote
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract arguments : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (admission : reached.plan.RawAdmission)
    (sourceTypeName : reached.sourceType = .base "Name")
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) payload =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).quoteConstructor [arguments]) :
    reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
  obtain ⟨sourceBound, targetBound, thinning, sourceAvailable, outer,
      sourceType, plan, skeletonContext, abstractEq⟩ := reached
  change sourceType = .base "Name" at sourceTypeName
  change plan.RawAdmission at admission
  cases plan with
  | bvar sourceIndex lookup correspondence availableScope =>
      cases canonical
  | fvar lookup =>
      cases canonical
  | boundaryApplication constructor rendered outsideCurrent certified
      certifies =>
      rename_i wireName rawArguments
      by_cases headEq : wireName =
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor
      · exact (outsideCurrent
          (CostHereditaryLeafDichotomyProbe.rhoRole_static_of_render_eq_quote
            constructor (rendered.trans headEq))).elim
      · rw [canonicalize_apply_of_ne_quote _ headEq] at canonical
        exact (headEq (Pattern.apply.inj canonical).1).elim
  | application constructor rendered current preimage notBare children =>
      by_cases labelEq : preimage.sourceConstructor.1.label =
          rhoReflectivePresentation.quoteConstructor
      · simp [CostStaticRegionPlan.rootClass, labelEq]
      · have processType := rho_applicationPlan_sourceType_eq_proc_of_not_quote
          (CostStaticRegionPlan.application constructor rendered current
            preimage notBare children) rfl labelEq
        have impossible : (TypeExpr.base "Name") = .base "Proc" :=
          sourceTypeName.symm.trans processType
        have nameEq : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
        contradiction
  | lambda bodyPlan =>
      cases sourceTypeName
  | multiLambda bodyPlan =>
      cases sourceTypeName
  | collection choice selected children =>
      have admissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) := by
        rw [sourceTypeName]
        exact rhoCanonicalRecursiveTypeDomain.base _
      have processType := rho_collectionPlan_sourceType_eq_proc
        (CostStaticRegionPlan.collection choice selected children)
          ⟨_, rfl⟩ admissible
      have impossible : (TypeExpr.base "Name") = .base "Proc" :=
        sourceTypeName.symm.trans processType
      have nameEq : ("Name" : String) = "Proc" := TypeExpr.base.inj impossible
      contradiction
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact (rho_boundaryCollection_choices_absurd color targetFree _ _ _ _
        oppositeSelected currentRejected).elim

/-- A left reached Quote whose process payload canonically exposes a Drop
closes against a right Quote when the shared canonical Name still has a Quote
root.  The exposed Name is sealed, so the recursive call may be transported
to the right endpoint's ambient availability. -/
noncomputable def quotePlanStops_commonRestorationApex_of_leftCanonicalDrop_rightCanonicalQuote
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftPayload rightPayload leftAbstract rightAbstract inner name
      nameArguments : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (leftPayloadShape : leftPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [inner])
    (canonicalInner : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) inner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [name])
    (nameQuote : name = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [nameArguments])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType))
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨innerAbstract, rawName, rawDropAbstract, nameAbstract, outerShape,
      abstractLeaves, rawDropShape, rawCanonical, rawNameSmaller, nameReached,
      _nameSourceBound, _nameTargetBound, _nameThinning, nameAvailable,
      nameType, nameAbstractEq, nameAdmission, ⟨nameEmbedding⟩⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_reachedName_of_quoteCanonicalDrop
      leftReached leftAdmission leftQuote leftPayloadShape canonicalInner
  have leftName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    leftReached.plan leftQuote
  have rightName : rightReached.sourceType = .base "Name" :=
    sourceTypeEq.symm.trans leftName
  have nameSourceTypeEq : nameReached.sourceType = rightReached.sourceType :=
    nameType.trans rightName.symm
  have outerCanonical : canonicalize declaration leftPayload = name := by
    rw [leftPayloadShape, canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    calc
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalize declaration inner] =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) canonicalInner
      _ = name := finishNormalizeReflectiveApply_quote_drop declaration name
  have recursiveCanonical : canonicalize declaration rawName =
      canonicalize declaration rightPayload :=
    rawCanonical.trans (outerCanonical.symm.trans canonical)
  have rawNameQuote : canonicalize declaration rawName =
      .apply declaration.quoteConstructor [nameArguments] :=
    rawCanonical.trans nameQuote
  have nameQuoteRoot :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.rootClass_eq_quote_of_name_canonical_quote
      nameReached nameAdmission nameType rawNameQuote
  have recursiveSmaller : sizeOf rawName + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 := by
    omega
  have recursiveApex :=
    quotePlanStops_commonRestorationApex_of_closeSmaller_supportCase leftView
      rightView closeSmaller (leftPayload := rawName)
      (rightPayload := rightPayload) (leftAbstract := nameAbstract)
      (rightAbstract := rightAbstract) nameReached rightReached
      nameAdmission rightAdmission
      nameAbstractEq rightAbstractEq nameSourceTypeEq
      (Or.inr (Or.inl nameAvailable))
      (nameEmbedding.comp leftEmbedding) rightEmbedding
      nameQuoteRoot rightQuote recursiveCanonical recursiveSmaller
      rightAdmissible callbackAvailable callbackScope callbackRoot
  rw [← nameAbstractEq] at recursiveApex
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftEndpointEq :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_eq_nameFrame_of_quoteCanonicalDrop
      leftView.node leftEnvironment
      (leftView.node.semanticAtom_typeMap leftValues leftInventory) cospan
      cospan.leftSlot cospan.leftCommutes leftReached nameReached leftAdmission
      leftEmbedding leftQuote nameType outerShape abstractLeaves
      rawDropShape nameAbstractEq callbackAvailable callbackScope
  subst leftAbstractEq
  subst rightAbstractEq
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _ at recursiveApex
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftEndpointEq.symm rfl recursiveApex

/-- Right-oriented companion of the one-sided canonical-Drop constructor. -/
noncomputable def quotePlanStops_commonRestorationApex_of_leftQuote_rightCanonicalDrop
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {leftPayload rightPayload leftAbstract rightAbstract inner name
      nameArguments : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries)
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightPayloadShape : rightPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [inner])
    (canonicalInner : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) inner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [name])
    (nameQuote : name = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [nameArguments])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨innerAbstract, rawName, rawDropAbstract, nameAbstract, outerShape,
      abstractLeaves, rawDropShape, rawCanonical, rawNameSmaller, nameReached,
      _nameSourceBound, _nameTargetBound, _nameThinning, nameAvailable,
      nameType, nameAbstractEq, nameAdmission, ⟨nameEmbedding⟩⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_reachedName_of_quoteCanonicalDrop
      rightReached rightAdmission rightQuote rightPayloadShape canonicalInner
  have rightName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    rightReached.plan rightQuote
  have leftName : leftReached.sourceType = .base "Name" :=
    sourceTypeEq.trans rightName
  have nameSourceTypeEq : leftReached.sourceType = nameReached.sourceType :=
    leftName.trans nameType.symm
  have outerCanonical : canonicalize declaration rightPayload = name := by
    rw [rightPayloadShape, canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    calc
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalize declaration inner] =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor [name]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child]) canonicalInner
      _ = name := finishNormalizeReflectiveApply_quote_drop declaration name
  have recursiveCanonical : canonicalize declaration leftPayload =
      canonicalize declaration rawName :=
    canonical.trans (outerCanonical.trans rawCanonical.symm)
  have rawNameQuote : canonicalize declaration rawName =
      .apply declaration.quoteConstructor [nameArguments] :=
    rawCanonical.trans nameQuote
  have nameQuoteRoot :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.rootClass_eq_quote_of_name_canonical_quote
      nameReached nameAdmission nameType rawNameQuote
  have recursiveSmaller : sizeOf leftPayload + sizeOf rawName <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 := by
    omega
  have nameAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) nameReached.sourceType) := by
    rw [nameType]
    exact rhoCanonicalRecursiveTypeDomain.base _
  have recursiveApex :=
    quotePlanStops_commonRestorationApex_of_closeSmaller_supportCase leftView
      rightView closeSmaller (leftPayload := leftPayload)
      (rightPayload := rawName) (leftAbstract := leftAbstract)
      (rightAbstract := nameAbstract) leftReached nameReached leftAdmission
      nameAdmission leftAbstractEq nameAbstractEq nameSourceTypeEq
      (Or.inr (Or.inr nameAvailable)) leftEmbedding
      (nameEmbedding.comp rightEmbedding) leftQuote nameQuoteRoot
      recursiveCanonical recursiveSmaller nameAdmissible callbackAvailable
      callbackScope callbackRoot
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have rightEndpointEq :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_eq_nameFrame_of_quoteCanonicalDrop
      rightView.node rightEnvironment
      (rightView.node.semanticAtom_typeMap rightValues rightInventory) cospan
      cospan.rightSlot cospan.rightCommutes rightReached nameReached
      rightAdmission rightEmbedding rightQuote nameType outerShape
      abstractLeaves rawDropShape nameAbstractEq callbackAvailable
      callbackScope
  rw [← nameAbstractEq] at recursiveApex
  subst leftAbstractEq
  subst rightAbstractEq
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _ at recursiveApex
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    rfl rightEndpointEq.symm recursiveApex

/-- Two reached Quotes whose process payloads both canonically expose Drops
close by descending to the two exact sealed Name plans and reindexing the
result through Quote/Drop absorption on both parent frames. -/
noncomputable def quotePlanStops_commonRestorationApex_of_canonicalDrops
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftPayload rightPayload leftAbstract rightAbstract leftInner rightInner
      leftName rightName : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (leftPayloadShape : leftPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [leftInner])
    (rightPayloadShape : rightPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [rightInner])
    (leftInnerCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftInner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [leftName])
    (rightInnerCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightInner =
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation).dropConstructor [rightName])
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨leftInnerAbstract, leftRawName, leftRawDropAbstract,
      leftNameAbstract, leftOuterShape, leftAbstractLeaves,
      leftRawDropShape, leftRawCanonical, leftRawSmaller, leftNameReached,
      leftNameSourceBound, leftNameTargetBound, leftNameThinning,
      leftNameAvailable, leftNameType, leftNameAbstractEq, leftNameAdmission,
      leftNameEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_reachedName_of_quoteCanonicalDrop
      leftReached leftAdmission leftQuote leftPayloadShape leftInnerCanonical
  obtain ⟨rightInnerAbstract, rightRawName, rightRawDropAbstract,
      rightNameAbstract, rightOuterShape, rightAbstractLeaves,
      rightRawDropShape, rightRawCanonical, rightRawSmaller, rightNameReached,
      rightNameSourceBound, rightNameTargetBound, rightNameThinning,
      rightNameAvailable, rightNameType, rightNameAbstractEq,
      rightNameAdmission, rightNameEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_reachedName_of_quoteCanonicalDrop
      rightReached rightAdmission rightQuote rightPayloadShape
        rightInnerCanonical
  obtain ⟨leftEmbedding'⟩ := leftEmbedding
  obtain ⟨rightEmbedding'⟩ := rightEmbedding
  obtain ⟨leftNameEmbedding'⟩ := leftNameEmbedding
  obtain ⟨rightNameEmbedding'⟩ := rightNameEmbedding
  have leftSourceName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    leftReached.plan leftQuote
  have rightSourceName := rho_applicationPlan_sourceType_eq_name_of_quoteRoot
    rightReached.plan rightQuote
  have leftNameSourceTypeEq : leftNameReached.sourceType =
      leftReached.sourceType := leftNameType.trans leftSourceName.symm
  have rightNameSourceTypeEq : rightNameReached.sourceType =
      rightReached.sourceType := rightNameType.trans rightSourceName.symm
  have nameSourceTypeEq : leftNameReached.sourceType =
      rightNameReached.sourceType :=
    leftNameSourceTypeEq.trans
      (sourceTypeEq.trans rightNameSourceTypeEq.symm)
  have nameSourceAvailableEq : leftNameReached.sourceAvailable =
      rightNameReached.sourceAvailable :=
    leftNameAvailable.trans rightNameAvailable.symm
  have nameSourceBoundEq : leftNameReached.sourceBound =
      rightNameReached.sourceBound :=
    leftNameSourceBound.trans
      (sourceBoundEq.trans rightNameSourceBound.symm)
  have nameTargetBoundEq : leftNameReached.targetBound =
      rightNameReached.targetBound :=
    leftNameTargetBound.trans
      (targetBoundEq.trans rightNameTargetBound.symm)
  have nameThinningEq : HEq leftNameReached.thinning
      rightNameReached.thinning :=
    leftNameThinning.trans (thinningEq.trans rightNameThinning.symm)
  have leftNameRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftNameReached.sourceType)) := by
    rw [leftNameSourceTypeEq]
    exact leftRoute
  have rightNameRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightNameReached.sourceType)) := by
    rw [rightNameSourceTypeEq]
    exact rightRoute
  have leftOuterCanonical : canonicalize declaration leftPayload =
      leftName := by
    rw [leftPayloadShape, canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    calc
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalize declaration leftInner] =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor [leftName]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child])
          leftInnerCanonical
      _ = leftName := finishNormalizeReflectiveApply_quote_drop declaration _
  have rightOuterCanonical : canonicalize declaration rightPayload =
      rightName := by
    rw [rightPayloadShape, canonicalize_apply_eq_finish]
    simp only [List.map_cons, List.map_nil]
    calc
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [canonicalize declaration rightInner] =
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
          declaration declaration.quoteConstructor
          [.apply declaration.dropConstructor [rightName]] :=
        congrArg
          (fun child =>
            Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
              declaration declaration.quoteConstructor [child])
          rightInnerCanonical
      _ = rightName := finishNormalizeReflectiveApply_quote_drop declaration _
  have namesCanonical : canonicalize declaration leftRawName =
      canonicalize declaration rightRawName :=
    leftRawCanonical.trans
      (leftOuterCanonical.symm.trans
        (canonical.trans
          (rightOuterCanonical.trans rightRawCanonical.symm)))
  have namesSmaller : sizeOf leftRawName + sizeOf rightRawName <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 := by
    omega
  have namesApex :=
    ParallelFrontier.sameColorReachedPair_commonRestorationApex leftView
      rightView rightRootAdmissible closeSmaller leftNameReached
      rightNameReached leftNameAdmission rightNameAdmission nameSourceTypeEq
      nameSourceAvailableEq nameSourceBoundEq nameTargetBoundEq nameThinningEq
      ⟨leftNameEmbedding'.comp leftEmbedding'⟩
      ⟨rightNameEmbedding'.comp rightEmbedding'⟩ leftNameRoute
      rightNameRoute namesCanonical
      (Nat.le_of_lt (lt_of_lt_of_le leftRawSmaller leftPayloadSizeLe))
      (Nat.le_of_lt (lt_of_lt_of_le rightRawSmaller rightPayloadSizeLe))
      namesSmaller callbackAvailable callbackScope callbackRoot
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  have leftEndpointEq :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_eq_nameFrame_of_quoteCanonicalDrop
      leftView.node leftEnvironment
      (leftView.node.semanticAtom_typeMap leftValues leftInventory) cospan
      cospan.leftSlot cospan.leftCommutes leftReached leftNameReached
      leftAdmission leftEmbedding' leftQuote leftNameType leftOuterShape
      leftAbstractLeaves leftRawDropShape leftNameAbstractEq callbackAvailable
      callbackScope
  have rightEndpointEq :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.parentCanonicalFrame_eq_nameFrame_of_quoteCanonicalDrop
      rightView.node rightEnvironment
      (rightView.node.semanticAtom_typeMap rightValues rightInventory) cospan
      cospan.rightSlot cospan.rightCommutes rightReached rightNameReached
      rightAdmission rightEmbedding' rightQuote rightNameType rightOuterShape
      rightAbstractLeaves rightRawDropShape rightNameAbstractEq
      callbackAvailable callbackScope
  subst leftAbstractEq
  subst rightAbstractEq
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration callbackRoot _ _ at namesApex
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftEndpointEq.symm rightEndpointEq.symm namesApex

/-- Two reached authored Quotes close in their parent semantic cospan when
their unique process arguments have the same selected-colour canonical form.
The recursive argument apex is formed at quote depth zero and then lifted
through the synchronized Quote finish. -/
noncomputable def quotePlanStops_commonRestorationApex_of_argumentCanonical
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftPayload rightPayload leftAbstract rightAbstract leftInner rightInner :
      Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (leftPayloadShape : leftPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [leftInner])
    (rightPayloadShape : rightPayload = .apply
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor [rightInner])
    (argumentCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftInner =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightInner)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨leftArgument, leftArgumentAbstract, leftShape, leftOuterShape,
      leftChild, leftChildSourceBound, leftChildTargetBound,
      leftChildThinning, leftChildAvailable, leftChildType,
      leftChildAbstractEq, leftChildAdmission, leftChildEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_quoteArgumentPlan
      leftReached leftAdmission leftQuote
  obtain ⟨rightArgument, rightArgumentAbstract, rightShape,
      rightOuterShape, rightChild, rightChildSourceBound,
      rightChildTargetBound, rightChildThinning, rightChildAvailable,
      rightChildType, rightChildAbstractEq, rightChildAdmission,
      rightChildEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_quoteArgumentPlan
      rightReached rightAdmission rightQuote
  have leftArgumentEq : leftArgument = leftInner := by
    exact (List.cons.inj
      (Pattern.apply.inj (leftShape.symm.trans leftPayloadShape)).2).1
  have rightArgumentEq : rightArgument = rightInner := by
    exact (List.cons.inj
      (Pattern.apply.inj (rightShape.symm.trans rightPayloadShape)).2).1
  subst leftArgument
  subst rightArgument
  obtain ⟨leftEmbedding'⟩ := leftEmbedding
  obtain ⟨rightEmbedding'⟩ := rightEmbedding
  obtain ⟨leftChildEmbedding'⟩ := leftChildEmbedding
  obtain ⟨rightChildEmbedding'⟩ := rightChildEmbedding
  obtain ⟨leftRoute'⟩ := leftRoute
  obtain ⟨rightRoute'⟩ := rightRoute
  let leftChildAtRoot := leftChild.rebaseAbstractRoot
    leftReached.skeletonContext (by
      calc
        leftView.node.plan.abstractPattern =
            leftReached.skeletonContext.fill
              leftReached.plan.abstractPattern := leftReached.abstract_eq
        _ = leftReached.skeletonContext.fill
              (.apply rhoReflectivePresentation.quoteConstructor
                [leftArgumentAbstract]) :=
          congrArg leftReached.skeletonContext.fill leftOuterShape)
  let rightChildAtRoot := rightChild.rebaseAbstractRoot
    rightReached.skeletonContext (by
      calc
        rightView.node.plan.abstractPattern =
            rightReached.skeletonContext.fill
              rightReached.plan.abstractPattern := rightReached.abstract_eq
        _ = rightReached.skeletonContext.fill
              (.apply rhoReflectivePresentation.quoteConstructor
                [rightArgumentAbstract]) :=
          congrArg rightReached.skeletonContext.fill rightOuterShape)
  have childSourceTypeEq : leftChildAtRoot.sourceType =
      rightChildAtRoot.sourceType := by
    exact leftChildType.trans rightChildType.symm
  have childSourceAvailableEq : leftChildAtRoot.sourceAvailable =
      rightChildAtRoot.sourceAvailable :=
    leftChildAvailable.trans rightChildAvailable.symm
  have childSourceBoundEq : leftChildAtRoot.sourceBound =
      rightChildAtRoot.sourceBound :=
    leftChildSourceBound.trans
      (sourceBoundEq.trans rightChildSourceBound.symm)
  have childTargetBoundEq : leftChildAtRoot.targetBound =
      rightChildAtRoot.targetBound :=
    leftChildTargetBound.trans
      (targetBoundEq.trans rightChildTargetBound.symm)
  have childThinningEq : HEq leftChildAtRoot.thinning
      rightChildAtRoot.thinning :=
    leftChildThinning.trans (thinningEq.trans rightChildThinning.symm)
  have leftChildRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftChildAtRoot.sourceType)) := by
    dsimp only [leftChildAtRoot,
      CostStaticPlanReached.rebaseAbstractRoot]
    rw [leftChildType]
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.quoteArgumentRoute
      leftReached leftQuote leftRoute'⟩
  have rightChildRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightChildAtRoot.sourceType)) := by
    dsimp only [rightChildAtRoot,
      CostStaticPlanReached.rebaseAbstractRoot]
    rw [rightChildType]
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.quoteArgumentRoute
      rightReached rightQuote rightRoute'⟩
  have leftArgumentSizeLe : sizeOf leftInner ≤
      sizeOf leftView.node.term.1 := by
    have childLt : sizeOf leftInner < sizeOf leftPayload := by
      rw [leftPayloadShape]
      simp_wf
      omega
    omega
  have rightArgumentSizeLe : sizeOf rightInner ≤
      sizeOf rightView.node.term.1 := by
    have childLt : sizeOf rightInner < sizeOf rightPayload := by
      rw [rightPayloadShape]
      simp_wf
      omega
    omega
  have argumentsSmaller : sizeOf leftInner + sizeOf rightInner <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 := by
    have leftLt : sizeOf leftInner < sizeOf leftPayload := by
      rw [leftPayloadShape]
      simp_wf
      omega
    have rightLt : sizeOf rightInner < sizeOf rightPayload := by
      rw [rightPayloadShape]
      simp_wf
      omega
    omega
  have childApex :=
    ParallelFrontier.sameColorReachedPair_commonRestorationApex leftView
      rightView rightRootAdmissible closeSmaller leftChildAtRoot
      rightChildAtRoot leftChildAdmission rightChildAdmission
      childSourceTypeEq childSourceAvailableEq childSourceBoundEq
      childTargetBoundEq childThinningEq
      ⟨leftChildEmbedding'.comp leftEmbedding'⟩
      ⟨rightChildEmbedding'.comp rightEmbedding'⟩ leftChildRoute
      rightChildRoute argumentCanonical leftArgumentSizeLe
      rightArgumentSizeLe argumentsSmaller 0 callbackScope 0
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftArgumentFrame :=
    cospan.reifyLeft leftEnvironment.lookupAtom?
      (leftView.node.thinning.thickenAmbientBVars callbackScope
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
              leftEnvironment)
            rhoReflectivePresentation.toReflectivePresentationDecl 0
              callbackScope
            (leftEnvironment.reify leftChildAtRoot.plan.abstractPattern))))
  let rightArgumentFrame :=
    cospan.reifyRight rightEnvironment.lookupAtom?
      (rightView.node.thinning.thickenAmbientBVars callbackScope
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
              rightEnvironment)
            rhoReflectivePresentation.toReflectivePresentationDecl 0
              callbackScope
            (rightEnvironment.reify rightChildAtRoot.plan.abstractPattern))))
  have childCommon : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      cospan declaration 0 leftArgumentFrame rightArgumentFrame := by
    change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration 0 _ _ at childApex
    exact childApex
  have argumentsApex :
      CostStaticAtomKeyCospan.CommonRestorationApexList rhoCIGSLT cospan
        declaration 0 [leftArgumentFrame] [rightArgumentFrame] :=
    .cons childCommon (.nil 0)
  have leftSupported : ConstructorListWithin (RhoCurrentStaticHead color)
      [leftArgumentFrame] := by
    have naturality :=
      ParallelFrontier.reached_parentCanonicalFrame_commonReify leftView.node
        leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
        leftChildAtRoot 0 callbackScope
    have frameEq : leftArgumentFrame =
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 0
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (leftEnvironment.reify
                  leftChildAtRoot.plan.abstractPattern)))) := by
      simpa only [leftArgumentFrame, CostStaticAtomKeyCospan.reifyLeft,
        declaration] using naturality
    refine ⟨?_, trivial⟩
    rw [frameEq]
    exact rho_plan_commonFrame_constructorsWithin leftView.node
      leftEnvironment leftView.node.thinning cospan cospan.leftSlot
      leftChildAtRoot.plan (leftChildEmbedding'.comp leftEmbedding')
      callbackScope 0
  have rightSupported : ConstructorListWithin (RhoCurrentStaticHead color)
      [rightArgumentFrame] := by
    have naturality :=
      ParallelFrontier.reached_parentCanonicalFrame_commonReify rightView.node
        rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
        rightChildAtRoot 0 callbackScope
    have frameEq : rightArgumentFrame =
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 0
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify
                  rightChildAtRoot.plan.abstractPattern)))) := by
      simpa only [rightArgumentFrame, CostStaticAtomKeyCospan.reifyRight,
        declaration] using naturality
    refine ⟨?_, trivial⟩
    rw [frameEq]
    exact rho_plan_commonFrame_constructorsWithin rightView.node
      rightEnvironment rightView.node.thinning cospan cospan.rightSlot
      rightChildAtRoot.plan (rightChildEmbedding'.comp rightEmbedding')
      callbackScope 0
  have finishesRestore :=
    ReflectiveContextSupport.restoresTogether_finishNormalizeReflectiveApply_quote_of_argumentsApex
      cospan declaration (RhoCurrentStaticHead color) (fun _ => True)
      (isQuoteConstructor_costStaticReflectivePresentationDecl color _ (by
        change rhoReflectivePresentation.toReflectivePresentationDecl ∈
          ReflectionExtension.rhoReflectionProfile.presentations
        simp [ReflectionExtension.rhoReflectionProfile]))
      (rho_currentStaticHead_reflectiveConstructorsAllowed color).drop
      (declC_dropNeQuote color)
      (CostCanonicalLaws.rho_costStatic_drop_isOrdinary color)
      (fun name _ => rhoNode_commonAssignment_rigidOrFixedQuote leftView.node
        rightView.node leftView.children rightView.children leftInventory
        rightInventory name)
      (fun {_leftName _rightName _depth} _ _ equality =>
        rhoNode_commonAssignments_restoreTogether leftView.node rightView.node
          leftView.children rightView.children leftInventory rightInventory
          (leftView.targetBound_eq_targetBound rightView) equality)
      argumentsApex leftSupported rightSupported (fun _ _ => True.intro)
      (fun _ _ => True.intro)
  have finishApex : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      cospan declaration callbackRoot
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor [leftArgumentFrame])
      (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply
        declaration declaration.quoteConstructor [rightArgumentFrame]) :=
    .leafAligned (.leaf finishesRestore)
  subst leftAbstractEq
  subst rightAbstractEq
  dsimp only [leftArgumentFrame, rightArgumentFrame, leftChildAtRoot,
    rightChildAtRoot, CostStaticPlanReached.rebaseAbstractRoot] at finishApex
  rw [leftChildAbstractEq, rightChildAbstractEq] at finishApex
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    declaration callbackRoot _ _
  rw [leftOuterShape, rightOuterShape]
  simpa [leftValues, rightValues, leftInventory, rightInventory,
    leftEnvironment, rightEnvironment, cospan, declaration,
    leftArgumentFrame, rightArgumentFrame, canonicalizeByDepths,
    canonicalizeListByDepths, canonicalizeListByDepths_eq_map,
    CostStaticAtomEnvironment.reify, Pattern.renameFVars, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
    CostStaticAtomKeyCospan.reifyWith, mapPatternList_eq_map, List.map_map,
    Function.comp_def, costStaticReflectivePresentationDecl_eq_map,
    ReflectionExtension.mapReflectivePresentation,
    Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapPattern_finishNormalizeReflectiveApply,
    Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.thickenAmbientBVars_finishNormalizeReflectiveApply,
    ReflectiveContextSupport.renameFVars_finishNormalizeReflectiveApply] using
      finishApex

/-- Exhaustive same-colour constructor for a pair of reached authored Quotes.
Quote/Drop absorption is handled by the sealed Name constructors, while the
retained-Quote arm descends to the unique process arguments. -/
noncomputable def quotePlanStops_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftQuote : leftReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  obtain ⟨leftInner, _leftInnerAbstract, leftPayloadShape,
      _leftOuterShape, _leftChild, _leftChildSourceBound,
      _leftChildTargetBound, _leftChildThinning, _leftChildAvailable,
      _leftChildType, _leftChildAbstractEq, _leftChildAdmission,
      _leftChildEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_quoteArgumentPlan
      leftReached leftAdmission leftQuote
  obtain ⟨rightInner, _rightInnerAbstract, rightPayloadShape,
      _rightOuterShape, _rightChild, _rightChildSourceBound,
      _rightChildTargetBound, _rightChildThinning, _rightChildAvailable,
      _rightChildType, _rightChildAbstractEq, _rightChildAdmission,
      _rightChildEmbedding⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanReached.exists_quoteArgumentPlan
      rightReached rightAdmission rightQuote
  obtain ⟨leftEmbedding'⟩ := leftEmbedding
  obtain ⟨rightEmbedding'⟩ := rightEmbedding
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) := by
    obtain ⟨rightRoute'⟩ := rightRoute
    exact CostCanonicalTypeRoute.rho_admissible rightRoute'
      rightRootAdmissible
  have quoteCanonical := canonical
  rw [leftPayloadShape, rightPayloadShape] at quoteCanonical
  rcases canonicalize_quote_app_cases declaration leftInner with
      ⟨leftName, leftDrop, leftOuter⟩ | leftRetained
  · rcases canonicalize_quote_app_cases declaration rightInner with
        ⟨rightName, rightDrop, rightOuter⟩ | rightRetained
    · exact quotePlanStops_commonRestorationApex_of_canonicalDrops leftView
        rightView rightRootAdmissible closeSmaller leftReached rightReached
        leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceBoundEq targetBoundEq thinningEq
        ⟨leftEmbedding'⟩ ⟨rightEmbedding'⟩ leftRoute rightRoute
        leftQuote rightQuote leftPayloadShape rightPayloadShape leftDrop
        rightDrop canonical leftPayloadSizeLe rightPayloadSizeLe
        callbackAvailable callbackScope callbackRoot
    · have nameQuote : leftName =
          .apply declaration.quoteConstructor
            [canonicalize declaration rightInner] :=
        leftOuter.symm.trans (quoteCanonical.trans rightRetained)
      exact
        quotePlanStops_commonRestorationApex_of_leftCanonicalDrop_rightCanonicalQuote
          leftView rightView closeSmaller leftReached rightReached
          leftAdmission rightAdmission leftAbstractEq rightAbstractEq
          sourceTypeEq leftEmbedding' rightEmbedding' leftQuote rightQuote
          leftPayloadShape leftDrop nameQuote canonical leftPayloadSizeLe
          rightPayloadSizeLe rightAdmissible callbackAvailable callbackScope
          callbackRoot
  · rcases canonicalize_quote_app_cases declaration rightInner with
        ⟨rightName, rightDrop, rightOuter⟩ | rightRetained
    · have nameQuote : rightName =
          .apply declaration.quoteConstructor
            [canonicalize declaration leftInner] :=
        rightOuter.symm.trans (quoteCanonical.symm.trans leftRetained)
      exact
        quotePlanStops_commonRestorationApex_of_leftQuote_rightCanonicalDrop
          leftView rightView closeSmaller leftReached rightReached
          leftAdmission rightAdmission leftAbstractEq rightAbstractEq
          sourceTypeEq leftEmbedding' rightEmbedding' leftQuote rightQuote
          rightPayloadShape rightDrop nameQuote canonical leftPayloadSizeLe
          rightPayloadSizeLe callbackAvailable callbackScope callbackRoot
    · have argumentsEq : canonicalize declaration leftInner =
          canonicalize declaration rightInner := by
        have outerEq := leftRetained.symm.trans
          (quoteCanonical.trans rightRetained)
        exact (List.cons.inj (Pattern.apply.inj outerEq).2).1
      exact quotePlanStops_commonRestorationApex_of_argumentCanonical
        leftView rightView rightRootAdmissible closeSmaller leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq
        rightAbstractEq sourceBoundEq targetBoundEq thinningEq
        ⟨leftEmbedding'⟩ ⟨rightEmbedding'⟩ leftRoute rightRoute
        leftQuote rightQuote leftPayloadShape rightPayloadShape argumentsEq
        leftPayloadSizeLe rightPayloadSizeLe callbackAvailable callbackScope
        callbackRoot

/-- A reached same-colour pair with a bare-parallel side closes at the
endpoint budget: every paired frontier leaf is strictly smaller than the
bare-parallel payload pair even when the payload pair itself occupies the
whole enclosing measure. -/
noncomputable def parallelPlanStops_commonRestorationApex_of_closeSmaller
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (parallel : RhoPlanStopParallelSideCell leftReached.plan.rootClass
      rightReached.plan.rootClass)
    (callbackAvailable callbackScope callbackRoot : Nat) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  obtain ⟨leftEmbedding'⟩ := leftEmbedding
  obtain ⟨rightEmbedding'⟩ := rightEmbedding
  obtain ⟨leftRoute'⟩ := leftRoute
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible rightRoute' rightRootAdmissible
  have leftAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact rightAdmissible
  have leftProcess : leftReached.sourceType = .base "Proc" := by
    rcases parallel with leftParallel | rightParallel
    · exact rho_collectionPlan_sourceType_eq_proc leftReached.plan
        ⟨rhoReflectivePresentation.parallelCollection, leftParallel⟩
        leftAdmissible
    · have rightProcess := rho_collectionPlan_sourceType_eq_proc
        rightReached.plan
        ⟨rhoReflectivePresentation.parallelCollection, rightParallel⟩
        rightAdmissible
      exact sourceTypeEq.trans rightProcess
  have parallelApex :=
    rho_reachedPlanPairCommonApex_of_sameColorCanonical leftView rightView
      callbackAvailable callbackScope callbackRoot leftReached rightReached
      leftAdmission rightAdmission sourceTypeEq sourceAvailableEq
      sourceBoundEq targetBoundEq thinningEq ⟨leftEmbedding'⟩
      ⟨rightEmbedding'⟩ leftProcess canonical (close := by
        dsimp only
        intro leftRaw leftEndpoint rightRaw rightEndpoint leftLeaf rightLeaf
          leafCanonical depth
        rcases leftLeaf with
          ⟨leftLeafAbstract, leftLeafMembership, leftLeafWitness,
            leftEndpointEq⟩
        rcases rightLeaf with
          ⟨rightLeafAbstract, rightLeafMembership, rightLeafWitness,
            rightEndpointEq⟩
        obtain ⟨leftLeafReached, leftLeafSourceBound, leftLeafTargetBound,
            leftLeafThinning, leftLeafAvailable, leftLeafProcess,
            leftLeafAbstractEq, leftLeafAdmission, ⟨leftLeafEmbedding⟩⟩ :=
          leftLeafWitness.exists_reached
        obtain ⟨rightLeafReached, rightLeafSourceBound,
            rightLeafTargetBound, rightLeafThinning, rightLeafAvailable,
            rightLeafProcess, rightLeafAbstractEq, rightLeafAdmission,
            ⟨rightLeafEmbedding⟩⟩ := rightLeafWitness.exists_reached
        let leftLeafAtRoot := leftLeafReached.rebaseAbstractRoot
          leftReached.skeletonContext leftReached.abstract_eq
        let rightLeafAtRoot := rightLeafReached.rebaseAbstractRoot
          rightReached.skeletonContext rightReached.abstract_eq
        have leafSourceTypeEq : leftLeafReached.sourceType =
            rightLeafReached.sourceType :=
          leftLeafProcess.trans rightLeafProcess.symm
        have leafSourceAvailableEq : leftLeafReached.sourceAvailable =
            rightLeafReached.sourceAvailable :=
          leftLeafAvailable.trans
            (sourceAvailableEq.trans rightLeafAvailable.symm)
        have leafSourceBoundEq : leftLeafReached.sourceBound =
            rightLeafReached.sourceBound :=
          leftLeafSourceBound.trans
            (sourceBoundEq.trans rightLeafSourceBound.symm)
        have leafTargetBoundEq : leftLeafReached.targetBound =
            rightLeafReached.targetBound :=
          leftLeafTargetBound.trans
            (targetBoundEq.trans rightLeafTargetBound.symm)
        have leafThinningEq : HEq leftLeafReached.thinning
            rightLeafReached.thinning :=
          leftLeafThinning.trans (thinningEq.trans rightLeafThinning.symm)
        have leftLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
            (mapTypeExpr (color.symbols rhoCIGSLT)
              (.base leftView.node.sourceSort.1))
            (mapTypeExpr (color.symbols rhoCIGSLT)
              leftLeafReached.sourceType)) := ⟨
          CostCanonicalTypeRoute.castEndpoint
            (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
              (leftProcess.trans leftLeafProcess.symm)) leftRoute'⟩
        have rightProcess : rightReached.sourceType = .base "Proc" :=
          sourceTypeEq.symm.trans leftProcess
        have rightLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
            (mapTypeExpr (color.symbols rhoCIGSLT)
              (.base rightView.node.sourceSort.1))
            (mapTypeExpr (color.symbols rhoCIGSLT)
              rightLeafReached.sourceType)) := ⟨
          CostCanonicalTypeRoute.castEndpoint
            (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
              (rightProcess.trans rightLeafProcess.symm)) rightRoute'⟩
        have bareParallel :
            (∃ elements, leftPayload = .collection
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation).parallelCollection elements none) ∨
            ∃ elements, rightPayload = .collection
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation).parallelCollection elements
                none := by
          rcases parallel with leftParallel | rightParallel
          · apply Or.inl
            apply ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
              leftReached leftAdmission
            simpa only [costStaticReflectivePresentationDecl_parallelCollection]
              using leftParallel
          · apply Or.inr
            apply ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
              rightReached rightAdmission
            simpa only [costStaticReflectivePresentationDecl_parallelCollection]
              using rightParallel
        have leafSmallerPayload :=
          ParallelFrontier.pair_sizeOf_lt_of_mem_parallelLeaves_of_bareParallel
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftLeafMembership rightLeafMembership bareParallel
        have leafSmallerRoot : sizeOf leftRaw + sizeOf rightRaw <
            sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 :=
          lt_of_lt_of_le leafSmallerPayload
            (Nat.add_le_add leftPayloadSizeLe rightPayloadSizeLe)
        have leftLeafSizeLeRoot : sizeOf leftRaw ≤
            sizeOf leftView.node.term.1 :=
          le_trans
            (ParallelFrontier.sizeOf_le_of_mem_parallelLeaves
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation)
              leftPayload leftRaw leftLeafMembership) leftPayloadSizeLe
        have rightLeafSizeLeRoot : sizeOf rightRaw ≤
            sizeOf rightView.node.term.1 :=
          le_trans
            (ParallelFrontier.sizeOf_le_of_mem_parallelLeaves
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation)
              rightPayload rightRaw rightLeafMembership) rightPayloadSizeLe
        have leafApex :=
          ParallelFrontier.sameColorReachedPair_commonRestorationApex
            leftView rightView rightRootAdmissible closeSmaller leftLeafAtRoot
            rightLeafAtRoot leftLeafAdmission rightLeafAdmission
            leafSourceTypeEq leafSourceAvailableEq leafSourceBoundEq
            leafTargetBoundEq leafThinningEq
            ⟨leftLeafEmbedding.comp leftEmbedding'⟩
            ⟨rightLeafEmbedding.comp rightEmbedding'⟩ leftLeafRoute
            rightLeafRoute leafCanonical leftLeafSizeLeRoot
            rightLeafSizeLeRoot leafSmallerRoot callbackAvailable
            callbackScope depth
        subst leftLeafAbstractEq
        subst rightLeafAbstractEq
        let leftEnvironment := CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let rightEnvironment := CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        have leftNaturality :=
          ParallelFrontier.reached_parentCanonicalFrame_commonReify
            leftView.node leftEnvironment cospan cospan.leftSlot
            cospan.leftCommutes leftLeafAtRoot callbackAvailable callbackScope
        have rightNaturality :=
          ParallelFrontier.reached_parentCanonicalFrame_commonReify
            rightView.node rightEnvironment cospan cospan.rightSlot
            cospan.rightCommutes rightLeafAtRoot callbackAvailable
            callbackScope
        have targetApex :=
          CostStaticAtomKeyCospan.CommonRestorationApex.reindex
            leftNaturality rightNaturality leafApex
        apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
          leftEndpointEq rightEndpointEq
        simpa only [leftEnvironment, rightEnvironment, cospan,
          leftLeafAtRoot, rightLeafAtRoot,
          CostStaticPlanReached.rebaseAbstractRoot,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using targetApex)
  simpa only [leftAbstractEq, rightAbstractEq] using parallelApex

/-- Same-colour plan stops at the successor budget restore in the enclosing
semantic cospan.  Strict payload pairs use ordinary reached-pair descent;
endpoint pairs are exhausted by the boundary, parallel, Quote, and variable
constructors. -/
noncomputable def rho_staticPlanStopCommonApex_of_sameColor_succ
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller color targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) :
    @RhoStaticPlanStopCommonApex targetFree available outer leftPattern
      rightPattern type left right color leftView rightView color
      (RhoCanonicalRawStop color
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 + 1)) := by
  intro availableDepth scopeDepth rootDepth leftAbstract rightAbstract stopped
  rcases stopped with ⟨leftPayload, rightPayload, evidence⟩
  rcases evidence with
    ⟨leftReached, rightReached, leftAdmission, rightAdmission,
      leftAbstractEq, rightAbstractEq, sourceTypeEq, sourceAvailableEq,
      sourceBoundEq, targetBoundEq, thinningEq, leftEmbedding,
      rightEmbedding, leftRoute, rightRoute, stopReason, leftPayloadSizeLe,
      rightPayloadSizeLe, rawAligned⟩
  have canonical := rawAligned.canonicalize_eq
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation) (fun given => given.1.2)
  by_cases smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1
  · have apex :=
      ParallelFrontier.sameColorReachedPair_commonRestorationApex leftView
        rightView rightRootAdmissible closeSmaller leftReached rightReached
        leftAdmission rightAdmission sourceTypeEq sourceAvailableEq
        sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding
        leftRoute rightRoute canonical leftPayloadSizeLe rightPayloadSizeLe
        smaller availableDepth scopeDepth rootDepth
    simpa only [leftAbstractEq, rightAbstractEq] using apex
  · by_cases bothBoundary :
        leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary
    · exact (smaller (rho_planStop_boundarySide_size_lt leftView.node
        rightView.node leftReached rightReached leftEmbedding rightEmbedding
        leftPayloadSizeLe rightPayloadSizeLe (Or.inl bothBoundary.1))).elim
    · have cell := rho_planStop_sharpCell leftReached rightReached
        (fun given => given.1.1) stopReason bothBoundary
      rcases rhoPlanStopCell_cases cell with boundary | parallel |
          quotePair | quoteSide
      · exact (smaller (rho_planStop_boundarySide_size_lt leftView.node
          rightView.node leftReached rightReached leftEmbedding rightEmbedding
          leftPayloadSizeLe rightPayloadSizeLe boundary)).elim
      · exact parallelPlanStops_commonRestorationApex_of_closeSmaller
          leftView rightView rightRootAdmissible closeSmaller leftReached
          rightReached leftAdmission rightAdmission leftAbstractEq
          rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
          targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
          rightRoute canonical leftPayloadSizeLe rightPayloadSizeLe parallel
          availableDepth scopeDepth rootDepth
      · exact quotePlanStops_commonRestorationApex leftView rightView
          rightRootAdmissible closeSmaller leftReached rightReached
          leftAdmission rightAdmission leftAbstractEq rightAbstractEq
          sourceTypeEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
          rightEmbedding leftRoute rightRoute quotePair.1 quotePair.2 canonical
          leftPayloadSizeLe rightPayloadSizeLe availableDepth scopeDepth
          rootDepth
      · have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
            (mapTypeExpr (color.symbols rhoCIGSLT)
              rightReached.sourceType) := by
          obtain ⟨rightRoute'⟩ := rightRoute
          exact CostCanonicalTypeRoute.rho_admissible rightRoute'
            rightRootAdmissible
        have leftNotBoundary :
            ¬ leftReached.plan.rootClass.IsCertifiedBoundary := by
          intro leftBoundary
          exact smaller (rho_planStop_boundarySide_size_lt leftView.node
            rightView.node leftReached rightReached leftEmbedding
            rightEmbedding leftPayloadSizeLe rightPayloadSizeLe
            (Or.inl leftBoundary))
        have rightNotBoundary :
            ¬ rightReached.plan.rootClass.IsCertifiedBoundary := by
          intro rightBoundary
          exact smaller (rho_planStop_boundarySide_size_lt leftView.node
            rightView.node leftReached rightReached leftEmbedding
            rightEmbedding leftPayloadSizeLe rightPayloadSizeLe
            (Or.inr rightBoundary))
        rcases rho_sameColorQuoteSide_quotePair_or_canonicalIsVariable
            leftReached rightReached sourceTypeEq rightAdmissible
            leftNotBoundary rightNotBoundary quoteSide.2 canonical with
            paired | variableCase
        · exact quotePlanStops_commonRestorationApex leftView rightView
            rightRootAdmissible closeSmaller leftReached rightReached
            leftAdmission rightAdmission leftAbstractEq rightAbstractEq
            sourceTypeEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
            rightEmbedding leftRoute rightRoute paired.1 paired.2 canonical
            leftPayloadSizeLe rightPayloadSizeLe availableDepth scopeDepth
            rootDepth
        · subst leftAbstractEq
          subst rightAbstractEq
          exact rho_reachedPlanPairCommonApex_of_sameColorVariable leftView
            rightView availableDepth scopeDepth rootDepth leftReached
            rightReached sourceBoundEq targetBoundEq thinningEq canonical
            variableCase

/-- Static collapsing views have the successor-budget plan-stop apex for
every declaration colour.  Same-colour endpoints use the explicit endpoint
cell constructors; foreign-colour stops use hereditary plan restoration. -/
theorem rho_collapsingViewsPlanStopApexInDomain
    (declarationColor : CostStaticColor) :
    RhoCollapsingViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible _leftWellSorted _rightWellSorted
    closeSmaller _collapsing _canonical
  have rightRootAdmissible := rightRootAdmissible_of_admissible rightView
    admissible
  have closeAtNodes : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1) := by
    rw [leftView.patternEq, rightView.patternEq]
    exact closeSmaller
  by_cases sameColor : color = declarationColor
  · subst color
    simpa only [leftView.patternEq, rightView.patternEq] using
      (rho_staticPlanStopCommonApex_of_sameColor_succ leftView rightView
        rightRootAdmissible closeAtNodes)
  · simpa only [leftView.patternEq, rightView.patternEq] using
      (rho_staticPlanStopCommonApex_of_foreign leftView rightView
        (Ne.symm sameColor) rightRootAdmissible closeAtNodes
        (parentMeasure := sizeOf leftView.node.term.1 +
          sizeOf rightView.node.term.1 + 1))

/-- Both generated declarations satisfy the collapsing plan-stop apex
obligation. -/
theorem rho_collapsingViewsPlanStopApexInDomain_allColors :
    ∀ color, RhoCollapsingViewsPlanStopApexInDomain color :=
  rho_collapsingViewsPlanStopApexInDomain

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
