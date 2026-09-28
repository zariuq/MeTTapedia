import Mettapedia.GSLT.LanguageDef.TypedOrderedRootPremiseActions
import Mettapedia.GSLT.Examples.TypedPartialSpinePremise

/-!
# A root query followed by a scoped reduction

This authored rule combines two different premise interpreters. The first
premise has two distinct equality-table results with identical endpoints;
the second reduces an open beta redex under two binders. Both histories must
survive even though they produce the same program state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.TypedMixedPremiseHistory

open Mettapedia.GSLT.LanguageDef.RestAwareTyping
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (openRedex)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine

private def term : TypeExpr := .base "Term"

def closedIdentity : Pattern :=
  .apply "Lam" [.lambda none (.bvar 0)]

def mixedSpec : RuleBindingSpec :=
  { dependencies := [("X", [term])],
    occurrences :=
      [{ «name» := "X", site := .right, path := [0, 0, 0, 0],
         arguments := [.bvar 0] },
       { «name» := "X", site := .premise 1 0 1, path := [],
         arguments := [.bvar 0] }] }

def mixedRule : RewriteRule :=
  { rule with
    «name» := "InnerCongAfterEquality",
    premises :=
      [.relationQuery "eq" [closedIdentity, closedIdentity],
       .scopedStep step],
    bindings := some mixedSpec }

def mixedLanguage : LanguageDef :=
  { language with «rewrites» := [mixedRule] }

private def free : FreeTypeContext :=
  FreeTypeContext.ofList mixedRule.typeContext

private theorem declared_dependencies (metaname : String)
    (dependencies : List TypeExpr)
    (found : dependencies? mixedSpec metaname = some dependencies) :
    dependencies = [term] := by
  by_cases named : metaname = "X"
  · subst metaname
    simpa [dependencies?, mixedSpec] using found.symm
  · have no : ("X" == metaname) = false := by
      simp [Ne.symm named]
    simp [dependencies?, mixedSpec, no] at found

private theorem typed_projection_empty
    (initial : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (root : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (before : AssignmentHasTypes mixedLanguage free mixedSpec [] initial)
    (projected : projectRoot? 0 initial = some root) : root = [] := by
  cases initial with
  | nil => simpa [projectRoot?] using projected.symm
  | cons head tail =>
      rcases head with ⟨metaname, value⟩
      obtain ⟨dependencies, resultType, declared, _, valueTyped⟩ :=
        before metaname value (by simp)
      have same : dependencies = [term] :=
        declared_dependencies metaname dependencies declared
      have valueDependencies : value.dependencies = [term] :=
        valueTyped.1.trans same
      have cannotProject : instantiateValue? value 0 0 [] = none := by
        simp [instantiateValue?, valueDependencies]
      simp [projectRoot?, cannotProject] at projected

theorem mixed_language_validates : mixedLanguage.validate = [] := by
  simp [LanguageDef.validate, mixedLanguage, mixedRule, language,
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
    TermParam.typeExpr, rule, step, closedIdentity, mixedSpec, term,
    Mettapedia.GSLT.Examples.ScopedLamCongExecution.openRedex]
  decide +kernel

theorem mixed_rule_schema_typed :
    RewriteHasType mixedLanguage mixedRule := by
  refine ⟨term, ?_, ?_⟩
  · exact checkSchemaHasType_sound (by decide +kernel)
  · exact checkSchemaHasType_sound (by decide +kernel)

def firstFiring : RuleFiring Unit :=
  { captured := [],
    completed := [("X", { dependencies := [term], ambient := 0,
                           body := .bvar 0 })],
    history := [.root 0 0, .step 1 0 ()],
    target := expected }

def secondFiring : RuleFiring Unit :=
  { firstFiring with history := [.root 0 1, .step 1 0 ()] }

theorem duplicate_query_rows :
    premiseStepWithEnv RelationEnv.empty mixedLanguage []
      (.relationQuery "eq" [closedIdentity, closedIdentity]) = [[], []] := by
  decide +kernel

theorem root_output_action :
    RootPremiseOutputAction mixedLanguage free mixedSpec []
      RelationEnv.empty
      (.relationQuery "eq" [closedIdentity, closedIdentity]) := by
  intro initial root raw before projected selected
  have emptyRoot := typed_projection_empty initial root before projected
  subst root
  rw [duplicate_query_rows] at selected
  have emptyRaw : raw = [] := by simpa using selected
  subst raw
  intro metaname result member
  simp at member

private theorem beta_outputs_typed (instantiated : Pattern)
    (evidence : Unit) (candidate : Pattern)
    (member : (evidence, candidate) ∈ localBetaOracle 2 instantiated) :
    HasType mixedLanguage free [term, term] candidate term := by
  by_cases same : instantiated = openRedex
  · subst instantiated
    simp [localBetaOracle,
      Mettapedia.GSLT.Examples.TypedPartialSpinePremise.beta_at_two] at member
    rcases member with ⟨_, rfl⟩
    exact HasType.bvar (by decide)
  · simp [localBetaOracle, same] at member

theorem scoped_action :
    PremiseTypeAction mixedLanguage free mixedRule mixedSpec []
      localBetaOracle RelationEnv.empty 1 (.scopedStep step) := by
  exact scopedStep_fvar_partialSpine_typeAction
    mixedLanguage free mixedRule mixedSpec [] [term] 1 step "X"
    [.bvar 0] [0] localBetaOracle RelationEnv.empty
    (by decide) (by decide) (by decide) (by decide)
    Mettapedia.GSLT.Examples.TypedPartialSpineCapture.selected_spine
    (by decide) (by
      intro instantiated evidence candidate member
      exact beta_outputs_typed instantiated evidence candidate member)

theorem ordered_actions :
    OrderedPremiseTypeActions mixedLanguage free mixedRule mixedSpec []
      localBetaOracle RelationEnv.empty 0 mixedRule.premises := by
  exact ⟨relationQuery_typeAction mixedLanguage free mixedRule mixedSpec
    [] localBetaOracle RelationEnv.empty 0 "eq"
    [closedIdentity, closedIdentity] root_output_action,
    scoped_action, trivial⟩

theorem exact_firings :
    applyRuleWithOracle localBetaOracle RelationEnv.empty
      mixedLanguage 0 mixedRule wrapped =
        [firstFiring, secondFiring] := by
  decide +kernel

private theorem empty_assignment_typed :
    AssignmentHasTypes mixedLanguage free mixedSpec [] [] := by
  intro metaname value member
  simp at member

/-- The selected runtime history itself is the input to the general ordered
typing theorem; no replacement history or reconstructed assignment is used. -/
theorem selected_run_keeps_types
    (final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment)
    (history : List (PremiseEvent Unit))
    (selected : (final, history) ∈ runPremises localBetaOracle
      RelationEnv.empty mixedLanguage mixedRule mixedSpec 0 0
      mixedRule.premises []) :
    AssignmentHasTypes mixedLanguage free mixedSpec [] final ∧
      history.length = 2 := by
  exact relationQuery_then_scopedStep_preserves_types
    mixedLanguage free mixedRule mixedSpec [] localBetaOracle
    RelationEnv.empty 0 "eq" [closedIdentity, closedIdentity] step
    [] final history root_output_action scoped_action
    empty_assignment_typed selected

theorem first_run_selected :
    (firstFiring.completed, firstFiring.history) ∈
      runPremises localBetaOracle RelationEnv.empty mixedLanguage
        mixedRule mixedSpec 0 0 mixedRule.premises [] := by
  decide +kernel

theorem second_run_selected :
    (secondFiring.completed, secondFiring.history) ∈
      runPremises localBetaOracle RelationEnv.empty mixedLanguage
        mixedRule mixedSpec 0 0 mixedRule.premises [] := by
  decide +kernel

theorem both_runtime_outputs_typed :
    AssignmentHasTypes mixedLanguage free mixedSpec []
        firstFiring.completed ∧
      AssignmentHasTypes mixedLanguage free mixedSpec []
        secondFiring.completed ∧
      firstFiring.history.length = 2 ∧
      secondFiring.history.length = 2 := by
  obtain ⟨firstTyped, firstLength⟩ :=
    selected_run_keeps_types firstFiring.completed firstFiring.history
      first_run_selected
  obtain ⟨secondTyped, secondLength⟩ :=
    selected_run_keeps_types secondFiring.completed secondFiring.history
      second_run_selected
  exact ⟨firstTyped, secondTyped, firstLength, secondLength⟩

theorem two_distinct_histories :
    ∃ first second,
      first ∈ applyRuleWithOracle localBetaOracle RelationEnv.empty
        mixedLanguage 0 mixedRule wrapped ∧
      second ∈ applyRuleWithOracle localBetaOracle RelationEnv.empty
        mixedLanguage 0 mixedRule wrapped ∧
      first.target = expected ∧ second.target = expected ∧
      first.history = [.root 0 0, .step 1 0 ()] ∧
      second.history = [.root 0 1, .step 1 0 ()] := by
  refine ⟨firstFiring, secondFiring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exact_firings]
    exact List.mem_cons_self
  · rw [exact_firings]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  all_goals rfl

theorem histories_are_distinct : firstFiring ≠ secondFiring := by
  decide +kernel

#print axioms duplicate_query_rows
#print axioms mixed_language_validates
#print axioms mixed_rule_schema_typed
#print axioms exact_firings
#print axioms selected_run_keeps_types
#print axioms both_runtime_outputs_typed
#print axioms two_distinct_histories
#print axioms histories_are_distinct

end Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
