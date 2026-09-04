import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

theorem rhoProc_boundaryPlan_canonical_escape_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern (.base "Proc"))
    (boundaryClass : plan.rootClass.IsCertifiedBoundary)
    (declarationColor : CostStaticColor) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
      declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
    RhoDescendEscape color (canonicalize declaration pattern) ∧
      canonicalize declaration pattern ≠
        .apply declaration.parallelUnitConstructor [] := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  generalize sourceTypeEq : (TypeExpr.base "Proc") = sourceType at plan
  cases plan with
  | boundaryApplication declared rendered outsideCurrent certified certifies =>
      subst sourceType
      rename_i wireName arguments
      have typed : HasType rhoCIGSLT.costWholeLanguage targetFree
          sourceAvailable (.apply wireName arguments)
          (mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc")) := by
        simpa only [certified.content_eq, certified.targetSupport_eq,
          certified.targetType_eq] using certified.typed.contentTyped
      by_cases quoteHead : wireName = declaration.quoteConstructor
      · have quoteRole := rhoRole_static_of_render_eq_quote declared
          (rendered.trans quoteHead)
        by_cases sameColor : declarationColor = color
        · subst declarationColor
          exact (outsideCurrent quoteRole).elim
        · have declarationFlip : declarationColor = color.flip :=
            CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
          subst declarationColor
          obtain ⟨rule, ruleMembership, labelEquality, _notBare,
              typeEquality, _argumentsTyped⟩ :=
            WellSorted.hasType_apply_inversion typed
          have categoryForm := rho_costWhole_rule_category_of_quoteWire
            color.flip ruleMembership
            (labelEquality.symm.trans
              (quoteHead.trans (rhoDecl_quoteConstructor color.flip)))
          have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
              mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Name") :=
            typeEquality.trans categoryForm
          exact (mapTypeExpr_cross_proc_ne color "Name" (by decide) cross).elim
      · have canonicalShape : canonicalize declaration
            (.apply wireName arguments) =
          .apply wireName (arguments.map (canonicalize declaration)) :=
          canonicalize_apply_of_ne_quote declaration quoteHead arguments
        have decodedNone : decodeDeclaredCostStaticConstructor rhoCIGSLT color
            wireName = none := by
          have decoded := decodeDeclaredCostStaticConstructor_render_of_role_ne
            rhoCIGSLT declared color outsideCurrent
          simpa only [rendered] using decoded
        constructor
        · constructor
          · intro collectionType elements rest equality
            rw [canonicalShape] at equality
            cases equality
          · exact ⟨wireName, arguments.map (canonicalize declaration),
              canonicalShape, decodedNone⟩
        · rw [canonicalShape]
          intro unitEquality
          have wireEq : wireName = declaration.parallelUnitConstructor :=
            (Pattern.apply.inj unitEquality).1
          have unitRole := rhoRole_static_of_render_eq_parallelUnit declared
            (rendered.trans wireEq)
          by_cases sameColor : declarationColor = color
          · subst declarationColor
            exact outsideCurrent unitRole
          · have declarationFlip : declarationColor = color.flip :=
              CostStaticColor.eq_flip_of_ne (Ne.symm sameColor)
            subst declarationColor
            obtain ⟨rule, ruleMembership, labelEquality, _notBare,
                typeEquality, _argumentsTyped⟩ :=
              WellSorted.hasType_apply_inversion typed
            have categoryForm := rho_costWhole_rule_category_of_unitWire
              color.flip ruleMembership
              (labelEquality.symm.trans
                (wireEq.trans (rhoDecl_unitConstructor color.flip)))
            have cross : mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") =
                mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Proc") :=
              typeEquality.trans categoryForm
            exact mapTypeExpr_flipProc_ne color (.base "Proc") cross.symm
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)
  | bvar | fvar | application | lambda | multiLambda | collection =>
      simp [CostStaticRegionPlan.rootClass,
        CostStaticPlanRootClass.IsCertifiedBoundary] at boundaryClass

theorem rho_rule_category_name_or_proc_canary {rule : GrammarRule}
    (membership : rule ∈ rhoCalc.terms) :
    rule.category = "Name" ∨ rule.category = "Proc" := by
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem rho_applicationPlan_sourceType_name_or_proc_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (applicationClass : ∃ constructor,
      plan.rootClass = .application constructor) :
    sourceType = .base "Name" ∨ sourceType = .base "Proc" := by
  cases plan with
  | application constructor rendered current preimage notBare children =>
      rcases rho_rule_category_name_or_proc_canary
          preimage.sourceConstructor.2 with category | category
      · exact Or.inl (congrArg TypeExpr.base category)
      · exact Or.inr (congrArg TypeExpr.base category)
  | bvar | fvar | boundaryApplication | lambda | multiLambda | collection |
      boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at applicationClass

theorem rho_collectionPlan_sourceType_eq_proc_canary
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (collectionClass : ∃ collectionType,
      plan.rootClass = .collection collectionType)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT) sourceType)) :
    sourceType = .base "Proc" := by
  cases plan with
  | collection choice selected children =>
      rename_i collectionType elements rest
      rcases mem_costStaticCollectionTypingChoices_sound rhoCIGSLT color
          targetFree targetBound collectionType elements
          (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) choice selected with
        direct | bare
      · rcases direct with
          ⟨sourceElementType, choiceEq, expectedEq, _elementsChecked⟩
        have sourceEq : sourceType =
            .collection collectionType sourceElementType :=
          mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEq
        subst sourceType
        exact (rhoCanonicalRecursiveTypeDomain.noCollection admissible).elim
      · rcases bare with
          ⟨rule, sourceElementType, choiceEq, membership, wrapped,
            expectedEq, parameterName, parameterShape, _elementsChecked⟩
        have sourceEq : sourceType = .base rule.category :=
          mapTypeExpr_costStatic_injective rhoCIGSLT color expectedEq
        rw [sourceEq, rho_bare_src_category rule membership
          ⟨parameterName, collectionType, sourceElementType, parameterShape⟩]
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd color targetFree targetBound _ _ _
          selected currentRejected)
  | bvar | fvar | boundaryApplication | application | lambda | multiLambda =>
      simp [CostStaticRegionPlan.rootClass] at collectionClass

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
