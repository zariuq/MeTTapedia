import Mettapedia.GSLT.LanguageDef.TypedOrderedPremiseExecution
import Mettapedia.GSLT.Examples.TypedPartialSpineCapture
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# Authored nested lambda congruence with a partial occurrence spine

The conditional premise reduces an open beta redex inside two binders. Its
result metavariable depends only on the inner binder. The checked beta oracle
supplies an open result, and the executor retains its event history. A result
depending on the omitted outer binder is rejected. The ordered-premise type
action is instantiated for this authored rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.TypedPartialSpinePremise

open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (openRedex betaOracle)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

private def term : TypeExpr := .base "Term"

def step : ScopedStepPremise :=
  { binders := [term, term], resultType := term,
    source := openRedex, target := .fvar "X" }

def rule : RewriteRule :=
  { «name» := "InnerCong",
    typeContext := [("X", term)], premises := [.scopedStep step],
    left := .apply "Lam" [.lambda none
      (.apply "Lam" [.lambda none openRedex])],
    right := .apply "Lam" [.lambda none
      (.apply "Lam" [.lambda none (.fvar "X")])],
    bindings := some
      { dependencies := [("X", [term])],
        occurrences :=
          [{ «name» := "X", site := .right, path := [0, 0, 0, 0],
             arguments := [.bvar 0] },
           { «name» := "X", site := .premise 0 0 1, path := [],
             arguments := [.bvar 0] }] } }

def language : LanguageDef :=
  { lambdaScoped with «rewrites» := [rule] }

private def spec : RuleBindingSpec :=
  rule.bindings.getD { dependencies := [] }

private def free : FreeTypeContext :=
  FreeTypeContext.ofList rule.typeContext

theorem authored_language_valid : language.validate = [] := by
  simp [LanguageDef.validate, language, lambdaScoped,
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
    TermParam.typeExpr, rule, step, term, openRedex]
  decide +kernel

theorem authored_binding_admitted : admittedFor rule spec = true := by
  decide +kernel

theorem beta_at_two : betaOracle 2 openRedex = [((), .bvar 0)] := by
  decide +kernel

/-- A filtered form of the actual authored beta oracle limits the premise
contract to the selected open redex. -/
def localBetaOracle : StepOracle Unit := fun depth source =>
  if depth == 2 && source == openRedex then betaOracle depth source else []

theorem beta_outputs_typed (instantiated : Pattern) (evidence : Unit)
    (candidate : Pattern)
    (member : (evidence, candidate) ∈ localBetaOracle 2 instantiated) :
    HasType language free [term, term] candidate term := by
  by_cases same : instantiated = openRedex
  · subst instantiated
    simp [localBetaOracle, beta_at_two] at member
    rcases member with ⟨_, rfl⟩
    exact HasType.bvar (by decide)
  · simp [localBetaOracle, same] at member

theorem premise_typeAction :
    PremiseTypeAction language free rule spec [] localBetaOracle
      RelationEnv.empty 0 (.scopedStep step) := by
  exact scopedStep_fvar_partialSpine_typeAction
    language free rule spec [] [term] 0 step "X" [.bvar 0] [0]
    localBetaOracle RelationEnv.empty
    (by decide) (by decide) (by decide) (by decide)
    Mettapedia.GSLT.Examples.TypedPartialSpineCapture.selected_spine
    (by decide) (by
      intro instantiated evidence candidate member
      exact beta_outputs_typed instantiated evidence candidate member)

theorem ordered_typeActions :
    OrderedPremiseTypeActions language free rule spec [] localBetaOracle
      RelationEnv.empty 0 rule.premises := by
  exact ⟨premise_typeAction, trivial⟩

theorem selected_run_keeps_types
    (initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (history : List (PremiseEvent Unit))
    (before : AssignmentHasTypes language free spec [] initial)
    (selected : (final, history) ∈ runPremises localBetaOracle
      RelationEnv.empty language rule spec 0 0 rule.premises initial) :
    AssignmentHasTypes language free spec [] final := by
  exact runPremises_preserves_assignment_types
    language free rule spec [] localBetaOracle RelationEnv.empty 0
    rule.premises initial final history ordered_typeActions before selected

def wrapped : Pattern :=
  .apply "Lam" [.lambda none (.apply "Lam" [.lambda none openRedex])]

def expected : Pattern :=
  .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.bvar 0)])]

theorem authored_rule_fires :
    ∃ firing ∈ applyRuleWithOracle localBetaOracle RelationEnv.empty
      language 0 rule wrapped,
      firing.target = expected ∧ firing.history = [.step 0 0 ()] := by
  decide +kernel

def omittedBinderOracle : StepOracle Unit := fun _ _ => [((), .bvar 1)]

theorem omitted_binder_output_rejected :
    applyRuleWithOracle omittedBinderOracle RelationEnv.empty
      language 0 rule wrapped = [] := by
  decide +kernel

#print axioms selected_run_keeps_types
#print axioms authored_rule_fires
#print axioms omitted_binder_output_rejected

end Mettapedia.GSLT.Examples.TypedPartialSpinePremise
