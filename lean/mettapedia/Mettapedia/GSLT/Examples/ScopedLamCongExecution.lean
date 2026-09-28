import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
import Mettapedia.GSLT.Examples.ScopedPremiseAuthoring

/-!
# Executing an authored lambda congruence premise below its binder

The inner beta step runs in the context extended by the outer lambda's
variable. A conditional LamCong rule consumes that event, recovers its open
result in the declared dependency context, and instantiates the enclosing
lambda. Two equal oracle endpoints retain distinct occurrence histories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

private def term : TypeExpr := .base "Term"

/-- The body metavariable depends on the beta lambda's bound argument. -/
def betaRule : RewriteRule :=
  { «name» := "Beta",
    typeContext := [("B", term), ("A", term)],
    premises := [],
    left := .apply "App"
      [.apply "Lam" [.lambda none (.fvar "B")], .fvar "A"],
    right := .subst (.fvar "B") (.fvar "A"),
    bindings := some
      { dependencies := [("B", [term]), ("A", [])],
        occurrences :=
        [{ «name» := "B", site := .left, path := [0, 0, 0],
           arguments := [.bvar 0] },
         { «name» := "B", site := .right, path := [0],
           arguments := [.bvar 0] }] } }

/-- A local step premise has its own binder; B and C both depend on it. -/
def lamCongRule : RewriteRule :=
  { «name» := "LamCong",
    typeContext := [("B", term), ("C", term)],
    premises :=
      [.scopedStep
        { binders := [term], resultType := term,
          source := .fvar "B", target := .fvar "C" }],
    left := .apply "Lam" [.lambda none (.fvar "B")],
    right := .apply "Lam" [.lambda none (.fvar "C")],
    bindings := some
      { dependencies := [("B", [term]), ("C", [term])],
        occurrences :=
        [{ «name» := "B", site := .left, path := [0, 0],
           arguments := [.bvar 0] },
         { «name» := "C", site := .right, path := [0, 0],
           arguments := [.bvar 0] },
         { «name» := "B", site := .premise 0 0 0, path := [],
           arguments := [.bvar 0] },
         { «name» := "C", site := .premise 0 0 1, path := [],
           arguments := [.bvar 0] }] } }

def language : LanguageDef :=
  { lambdaScoped with «rewrites» := [betaRule, lamCongRule] }

def localStep : ScopedStepPremise :=
  { binders := [term], resultType := term,
    source := .fvar "B", target := .fvar "C" }

/-- The premise used by execution is also accepted by the declaration-derived
sorted compiler, at its one-variable local context. -/
theorem lamCong_premise_compiles :
    compileRulePremises? language lamCongRule = some [.step localStep] := by
  simp [compileRulePremises?, compileList?, compile?,
    Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise.check,
    Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType,
    localStep, language, lambdaScoped,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, LanguageDef.ofCore,
    lamCongRule, term]
  decide +kernel

/-- The two rules are admitted together by the authored language validator,
not only by the binding checker for a chosen individual rule. -/
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
    TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    betaRule, lamCongRule, term]
  decide +kernel

theorem authored_binding_declarations_valid :
    bindingDeclarationsValid language = true := by
  unfold bindingDeclarationsValid
  rw [authored_language_valid]
  simp only [List.isEmpty_nil, Bool.true_and]
  simp [language, betaRule, lamCongRule, lambdaScoped,
    LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
    LanguageDef.nullaryLabels, LanguageDef.ofCore,
    admittedFor, dependencySortsDeclared, occurrenceDepthAtSite?,
    siteBinderDepth?, sitePattern?, occurrenceDepthAt?, quantifiedBody?,
    dependencies?, Pattern.isGroundAt, LanguageDef.typeNames, term]
  decide +kernel

/-- The local premise sites really have depth one, including the root of
their endpoint patterns. -/
theorem premise_site_depths :
    occurrenceDepthAtSite? lamCongRule (.premise 0 0 0) [] = some 1 ∧
    occurrenceDepthAtSite? lamCongRule (.premise 0 0 1) [] = some 1 := by
  decide +kernel

/-- The exact authored occurrence declarations, including #0 inside the
premise, pass the executable binding admission check. -/
theorem lamCong_binding_admitted :
    admittedFor lamCongRule
      { dependencies := [("B", [term]), ("C", [term])],
        occurrences :=
          [{ «name» := "B", site := .left, path := [0, 0],
             arguments := [.bvar 0] },
           { «name» := "C", site := .right, path := [0, 0],
             arguments := [.bvar 0] },
           { «name» := "B", site := .premise 0 0 0, path := [],
             arguments := [.bvar 0] },
           { «name» := "C", site := .premise 0 0 1, path := [],
             arguments := [.bvar 0] }] } = true := by
  decide +kernel

/-- The actual beta rule supplies a one-step oracle in any ambient context. -/
def betaOracle : StepOracle Unit := fun ambient source =>
  (applyRuleWithOracle (Evidence := Unit) (fun _ _ => []) RelationEnv.empty language
    ambient betaRule source).map fun firing => ((), firing.target)

def openRedex : Pattern :=
  .apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]

def wrappedRedex : Pattern :=
  .apply "Lam" [.lambda none openRedex]

def wrappedTarget : Pattern :=
  .apply "Lam" [.lambda none (.bvar 0)]

/-- Beta really executes in the premise's extended context; its output keeps
the variable bound by the surrounding lambda. -/
theorem inner_beta_open : betaOracle 1 openRedex = [((), .bvar 0)] := by
  decide +kernel

/-- The complete one-fuel executor has exactly the bound variable as its
open beta result. The history remains an independent witness. -/
theorem inner_beta_targets :
    (rewriteAt RelationEnv.empty language 1 1 openRedex).map Prod.snd =
      [.bvar 0] := by
  decide +kernel

/-- This theorem checks the full conditional execution route, rather than a
separate handwritten lambda relation. -/
theorem lamCong_executes_open :
    ∃ firing ∈ applyRuleWithOracle betaOracle RelationEnv.empty language
      0 lamCongRule wrappedRedex,
      firing.target = wrappedTarget ∧ firing.history.length = 1 := by
  decide +kernel

/-- The same result is reached by the generic fuel-indexed evaluator of the
authored rule list, with Beta as the nested rule rather than a hand-supplied
premise answer. One layer is insufficient for that nested firing. -/
theorem lamCong_requires_two_layers :
    ((rewriteAt RelationEnv.empty language 1 0 wrappedRedex).map Prod.snd) = [] ∧
    wrappedTarget ∈
      ((rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map Prod.snd) := by
  decide +kernel

/-- Inspect the whole two-layer history, including the selected LamCong
rule, its premise position, and the nested Beta rule. -/
def lamCongBetaHistory : RuleHistory → Bool
  | .fire 1 [.step 0 0 (.fire 0 [])] => true
  | _ => false

theorem lamCong_tree_shape :
    (rewriteAt RelationEnv.empty language 2 0 wrappedRedex).map
      (fun (history, target) =>
        (lamCongBetaHistory history, target == wrappedTarget)) =
      [(true, true)] := by
  decide +kernel

/-- A result referring to an unavailable second local variable is discarded
before it can be captured as C. -/
def escapingOracle : StepOracle Unit := fun _ _ => [((), .bvar 1)]

theorem escaping_output_rejected :
    applyRuleWithOracle escapingOracle RelationEnv.empty language
      0 lamCongRule wrappedRedex = [] := by
  decide +kernel

/-- Equal endpoints from two oracle occurrences remain separate firing
histories at the outer conditional rule. -/
def duplicateOracle : StepOracle Unit :=
  fun _ _ => [((), .bvar 0), ((), .bvar 0)]

theorem duplicate_histories_retained :
    ∃ first second,
      applyRuleWithOracle duplicateOracle RelationEnv.empty language
        0 lamCongRule wrappedRedex = [first, second] ∧
      first.target = wrappedTarget ∧ second.target = wrappedTarget ∧
      first.history ≠ second.history := by
  let firings := applyRuleWithOracle duplicateOracle RelationEnv.empty language
    0 lamCongRule wrappedRedex
  have hlength : firings.length = 2 := by decide +kernel
  obtain ⟨first, second, hlist⟩ := List.length_eq_two.mp hlength
  have htargets : firings.map (·.target) =
      [wrappedTarget, wrappedTarget] := by decide +kernel
  have hhistories : firings.map (·.history) =
      [[.step 0 0 ()], [.step 0 1 ()]] := by decide +kernel
  simp only [hlist, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at htargets hhistories
  exact ⟨first, second, hlist, htargets.1, htargets.2,
    fun equal => by
      have unequal : ([.step 0 0 ()] : List (PremiseEvent Unit)) ≠
          [.step 0 1 ()] := by decide
      apply unequal
      calc
        [.step 0 0 ()] = first.history := hhistories.1.symm
        _ = second.history := equal
        _ = [.step 0 1 ()] := hhistories.2⟩

end Mettapedia.GSLT.Examples.ScopedLamCongExecution
