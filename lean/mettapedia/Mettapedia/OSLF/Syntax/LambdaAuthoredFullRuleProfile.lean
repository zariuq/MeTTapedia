import Mettapedia.OSLF.Syntax.LambdaAuthoredLamCongExecutionComparison

/-!
# The complete authored four-rule lambda profile

The existing executable lambda profile has Beta and binder-local LamCong.
This extension adds both application congruence rules without changing the
earlier declarations or their positions. Each recursive premise declares its
own empty local binder context and result sort; the lambda premise in the
existing profile retains its nonempty local context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

private def termType : TypeExpr := .base "Term"

/-- Empty-dependency occurrence contexts for application-left congruence. -/
def appCongLSpec : RuleBindingSpec :=
  { dependencies := [("F", []), ("G", []), ("A", [])],
    occurrences :=
    [{ «name» := "F", site := .left, path := [0], arguments := [] },
     { «name» := "A", site := .left, path := [1], arguments := [] },
     { «name» := "G", site := .right, path := [0], arguments := [] },
     { «name» := "A", site := .right, path := [1], arguments := [] },
     { «name» := "F", site := .premise 0 0 0, path := [],
       arguments := [] },
     { «name» := "G", site := .premise 0 0 1, path := [],
       arguments := [] }] }

/-- Empty-dependency occurrence contexts for application-right congruence. -/
def appCongRSpec : RuleBindingSpec :=
  { dependencies := [("F", []), ("A", []), ("B", [])],
    occurrences :=
    [{ «name» := "F", site := .left, path := [0], arguments := [] },
     { «name» := "A", site := .left, path := [1], arguments := [] },
     { «name» := "F", site := .right, path := [0], arguments := [] },
     { «name» := "B", site := .right, path := [1], arguments := [] },
     { «name» := "A", site := .premise 0 0 0, path := [],
       arguments := [] },
     { «name» := "B", site := .premise 0 0 1, path := [],
       arguments := [] }] }

def appCongLStep : ScopedStepPremise :=
  { binders := [], resultType := termType,
    source := .fvar "F", target := .fvar "G" }

def appCongRStep : ScopedStepPremise :=
  { binders := [], resultType := termType,
    source := .fvar "A", target := .fvar "B" }

/-- The recursive left-application premise has no new binder and returns a
term. Its output metavariable is supplied by the premise, not the left side. -/
def appCongLRule : RewriteRule :=
  { «name» := "AppCongL",
    typeContext := [("F", termType), ("G", termType), ("A", termType)],
    premises := [.scopedStep appCongLStep],
    left := .apply "App" [.fvar "F", .fvar "A"],
    right := .apply "App" [.fvar "G", .fvar "A"],
    bindings := some appCongLSpec }

/-- The right-application premise steps the argument; the function position
is a repeated ambient capture and is not substituted by premise output. -/
def appCongRRule : RewriteRule :=
  { «name» := "AppCongR",
    typeContext := [("F", termType), ("A", termType), ("B", termType)],
    premises := [.scopedStep appCongRStep],
    left := .apply "App" [.fvar "F", .fvar "A"],
    right := .apply "App" [.fvar "F", .fvar "B"],
    bindings := some appCongRSpec }

/-- All four Chapter 7 lambda reductions in one executable authored
language. Existing Beta and LamCong retain their former rule positions. -/
def language : LanguageDef :=
  { Mettapedia.GSLT.Examples.ScopedLamCongExecution.language with
    «rewrites» :=
      [Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
       Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
       appCongLRule, appCongRRule] }

theorem prior_rules_prefix :
    language.rewrites.take 2 =
      Mettapedia.GSLT.Examples.ScopedLamCongExecution.language.rewrites := by
  rfl

theorem authored_rule_names :
    language.rewrites.map RewriteRule.name =
      ["Beta", "LamCong", "AppCongL", "AppCongR"] := by
  rfl

theorem appCongL_binding_admitted :
    admittedFor appCongLRule appCongLSpec = true := by
  decide +kernel

theorem appCongR_binding_admitted :
    admittedFor appCongRRule appCongRSpec = true := by
  decide +kernel

/-- The complete four-rule declaration passes the same authored-language
validator as the two-rule prefix. -/
theorem authored_language_valid : language.validate = [] := by
  simp [LanguageDef.validate, language,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
    Mettapedia.GSLT.Examples.ScopedPremiseAuthoring.lambdaScoped,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, LanguageDef.ofCore,
    RewriteRule.resolveNullary, Premise.resolveNullary,
    Pattern.resolveNullary, Pattern.resolveNullaryList,
    Pattern.eraseBinderMetadata,
    LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors, LanguageDef.premisePatterns,
    LanguageDef.premiseLocallyScoped, LanguageDef.premiseStepTypeExprs,
    LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
    LanguageDef.premiseForAllParams, LanguageDef.patternFvarNames,
    LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, LanguageDef.typeNames,
    TypeExpr.baseNames, TermParam.bodyName, TermParam.binderNames,
    TermParam.typeExpr,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.lamCongRule,
    appCongLRule, appCongRRule,
    appCongLStep, appCongRStep, termType]
  decide +kernel

theorem authored_binding_declarations_valid :
    bindingDeclarationsValid language = true := by
  unfold bindingDeclarationsValid
  rw [authored_language_valid]
  simp only [List.isEmpty_nil, Bool.true_and]
  simp [language, appCongLRule, appCongRRule, appCongLSpec,
    appCongRSpec, appCongLStep, appCongRStep,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.language,
    Mettapedia.GSLT.Examples.ScopedPremiseAuthoring.lambdaScoped,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, LanguageDef.ofCore,
    admittedFor, dependencySortsDeclared, occurrenceDepthAtSite?,
    siteBinderDepth?, sitePattern?, occurrenceDepthAt?, quantifiedBody?,
    dependencies?, LanguageDef.typeNames, termType]
  decide +kernel

/-- Both application premises elaborate to explicitly sorted, empty-local-
context steps. The binder-local LamCong premise stays separate. -/
theorem appCongL_premise_compiles :
    compileRulePremises? language appCongLRule =
      some [.step appCongLStep] := by
  decide +kernel

theorem appCongR_premise_compiles :
    compileRulePremises? language appCongRRule =
      some [.step appCongRStep] := by
  decide +kernel

#print axioms prior_rules_prefix
#print axioms appCongL_binding_admitted
#print axioms appCongR_binding_admitted
#print axioms authored_language_valid
#print axioms authored_binding_declarations_valid
#print axioms appCongL_premise_compiles
#print axioms appCongR_premise_compiles

end Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
