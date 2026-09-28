import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# Authored lambda congruence with a local step premise

The authored notation supplies a premise-local binder sort and a common
endpoint sort. The DSL lowers it to the same canonical payload checked by the
sorted rule compiler. The escaping-variable control fails that compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedPremiseAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise

section
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- The surface declaration retains its lambda-body step as a scoped premise. -/
def lambdaScoped : LanguageDef :=
  languageDef! {
    name : "LambdaScoped"
    types { Term }
    terms {
      App . f:Term, a:Term |- f a : Term;
      Lam . ^x.body:[Term -> Term] |- "lam" body : Term;
    }
    equations { }
    rewrites {
      LamCong . | scopedStep([Term], Term,
          App(Lam(^y.(#0)), #0), #0)
        |- Lam(^x.(App(Lam(^y.(#0)), #0))) ~> Lam(^x.(#0));
    }
  }

end

def authoredRule : RewriteRule :=
  lambdaScoped.rewrites.get ⟨0, by decide⟩

def dslBodyStep : ScopedStepPremise where
  binders := [.base "Term"]
  resultType := .base "Term"
  source := .apply "App"
    [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]
  target := .bvar 0

theorem authored_rule_is_scoped :
    authoredRule.premises = [.scopedStep dslBodyStep] := by
  simp [authoredRule, lambdaScoped, LanguageDef.resolveNullaryPatterns,
    LanguageDef.resolveNullaryWith, LanguageDef.nullaryLabels,
    LanguageDef.ofCore, RewriteRule.resolveNullary, Premise.resolveNullary,
    Pattern.resolveNullary, Pattern.resolveNullaryList,
    Pattern.eraseBinderMetadata, dslBodyStep]

theorem authored_rule_compiles :
    compileRulePremises? lambdaScoped authoredRule =
      some [.step dslBodyStep] := by
  simp [compileRulePremises?, authoredRule,
    lambdaScoped, LanguageDef.resolveNullaryPatterns,
    LanguageDef.resolveNullaryWith, LanguageDef.nullaryLabels,
    LanguageDef.ofCore, RewriteRule.resolveNullary, Premise.resolveNullary,
    Pattern.resolveNullary, Pattern.resolveNullaryList,
    Pattern.eraseBinderMetadata, dslBodyStep,
    compileList?, compile?, check,
    Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType]
  decide +kernel

theorem authored_rule_valid : lambdaScoped.validate = [] := by
  simp [LanguageDef.validate, lambdaScoped, LanguageDef.ofCore,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, RewriteRule.resolveNullary,
    Premise.resolveNullary, Pattern.resolveNullary,
    Pattern.resolveNullaryList,
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
    TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr]
  decide +kernel

/-- A premise that escapes its one local binder is rejected at admission. -/
theorem escaping_rejected :
    compile? lambdaScoped
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty []
      (.scopedStep { dslBodyStep with target := .bvar 1 }) = none := by
  decide +kernel

end Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
