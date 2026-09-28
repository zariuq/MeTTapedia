import Mettapedia.GSLT.Examples.TypedPremiseOutput

/-!
# Binding admission does not imply sorted execution

The scoped executor checks that a rule's binding specification is structurally
admitted. That check is independent of the authored result sort. The original
premise-output capture regression is a concrete counterexample: its source is
a term of the declared base sort, while its executed reduct is an arrow-typed
lambda. The sorted variant of the same regression supplies the positive
control. A preservation theorem must use schema typing as well as the binding
and premise contracts.
-/

namespace Mettapedia.GSLT.Examples.ScopedExecutionSortingBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestAwareTyping (HasType checkSchemaHasType_sound)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

set_option autoImplicit false

private abbrev rawLanguage : LanguageDef :=
  Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage

private abbrev rawRule : RewriteRule :=
  Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule

private def input : Pattern := .apply "f" [.apply "a" []]
private def output : Pattern := .lambda none (.apply "a" [])

theorem raw_input_typed :
    HasType rawLanguage FreeTypeContext.empty [] input (.base "Term") :=
  checkSchemaHasType_sound (by decide +kernel)

theorem raw_output_not_typed :
    ¬ HasType rawLanguage FreeTypeContext.empty [] output (.base "Term") := by
  intro typed
  cases typed

private theorem raw_language_validates : rawLanguage.validate = [] := by
  simp [LanguageDef.validate, rawLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputLanguage,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputRule,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTerm, LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns, LanguageDef.typeNames,
    TypeDecl.plain, TypeExpr.term, TypeExpr.baseType,
    TypeExpr.baseNames, TermParam.bodyName, TermParam.binderNames,
    TermParam.typeExpr, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  decide +kernel

private theorem raw_bindings_valid :
    Mettapedia.OSLF.MeTTaIL.RuleBinding.bindingDeclarationsValid
      rawLanguage = true := by
  unfold Mettapedia.OSLF.MeTTaIL.RuleBinding.bindingDeclarationsValid
  rw [raw_language_validates]
  decide +kernel

theorem raw_binding_admitted :
    scopedRewritesExecutable rawLanguage = true := by
  unfold scopedRewritesExecutable
  rw [raw_bindings_valid]
  simp [rawLanguage, Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputLanguage,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputRule]
  decide +kernel

theorem raw_rule_fires :
    output ∈ applyRuleAt RelationEnv.empty rawLanguage 0 rawRule input := by
  rw [show applyRuleAt RelationEnv.empty rawLanguage 0 rawRule input = [output] from
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.closed_premise_output_stays_closed]
  simp

/-- An actual admitted closed rule fires from a typed source to a reduct that
does not have the same result sort. Binding admission alone cannot imply
result-sort preservation. -/
theorem binding_admission_does_not_imply_sort_preservation :
    ∃ (language : LanguageDef) (rule : RewriteRule)
        (source target : Pattern) (resultType : TypeExpr),
      scopedRewritesExecutable language = true ∧
      rule ∈ language.rewrites ∧
      HasType language FreeTypeContext.empty [] source resultType ∧
      target ∈ applyRuleAt RelationEnv.empty language 0 rule source ∧
      ¬ HasType language FreeTypeContext.empty [] target resultType := by
  refine ⟨rawLanguage, rawRule, input, output, .base "Term",
    raw_binding_admitted, ?_, raw_input_typed, raw_rule_fires,
    raw_output_not_typed⟩
  simp [rawLanguage, Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputLanguage,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputRule]

/-- Adding the authored result-sort discipline repairs this particular
regression while preserving its open-variable behavior. -/
theorem sorted_variant_keeps_its_result_sort :
    ∃ source target : Pattern,
      HasType Mettapedia.GSLT.Examples.TypedPremiseOutput.sortedPremiseLanguage
        FreeTypeContext.empty [.base "Term"] source
        (.arrow (.base "Term") (.base "Term")) ∧
      target ∈ applyRuleAt RelationEnv.empty
        Mettapedia.GSLT.Examples.TypedPremiseOutput.sortedPremiseLanguage 1
        Mettapedia.GSLT.Examples.TypedPremiseOutput.sortedPremiseRule source ∧
      HasType Mettapedia.GSLT.Examples.TypedPremiseOutput.sortedPremiseLanguage
        FreeTypeContext.empty [.base "Term"] target
        (.arrow (.base "Term") (.base "Term")) := by
  refine ⟨Mettapedia.GSLT.Examples.TypedPremiseOutput.openInput,
    Mettapedia.GSLT.Examples.TypedPremiseOutput.openOutput,
    Mettapedia.GSLT.Examples.TypedPremiseOutput.openInputTyped, ?_,
    Mettapedia.GSLT.Examples.TypedPremiseOutput.openOutputTyped⟩
  rw [Mettapedia.GSLT.Examples.TypedPremiseOutput.openPremiseOutputKeepsAmbientVariable]
  simp

#print axioms binding_admission_does_not_imply_sort_preservation
#print axioms sorted_variant_keeps_its_result_sort

end Mettapedia.GSLT.Examples.ScopedExecutionSortingBoundary
