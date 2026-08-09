import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Adequacy of the authored MeTTa Zero language

`MeTTaZero.language` is the authored five-field presentation.  Its two
relation premises are realized here from the semantic kernel, with evaluation
computed exclusively by `MeTTaZero.evaluateOne`, hence ultimately by public
query plus the declared grounding portal.

The generic MeTTaIL rule engine preserves the semantic occurrence bag.  It may
enumerate that bag in an arbitrary representative order, but coercing the
result back to a multiset recovers the query and evaluation GSLTs exactly.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The generic executor and the total GSLT use one relation environment.
This abbreviation deliberately introduces no second semantic authority. -/
noncomputable abbrev relationEnv (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : RelationEnv :=
  semanticRelationEnv model space spaceTerm

/-- Both authored Zero rules use only host-supplied relation queries.  Thus
the contextual closure adds no hidden recursive reduction to the root
query/evaluation behavior. -/
private theorem zero_rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites →
      NoncontextualPremises rule.premises := by
  intro rule ruleMember
  change rule ∈ [queryRewrite, evaluationRewrite] at ruleMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
  rcases ruleMember with rfl | rfl
  all_goals exact .relationQuery .nil

/-- Root-step evidence is precisely membership in the generic root executor. -/
private theorem rootStep_iff_mem_executor (relEnv : RelationEnv)
    (source target : Pattern) :
    RootStep relEnv language source target ↔
      target ∈ rewriteStepWithPremisesUsing relEnv language source := by
  simp [RootStep, rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing]

/-- The combined Zero GSLT and the generic root executor expose exactly the
same one-step relation. -/
theorem totalTheory_step_iff_mem_executor (model : Model)
    (space : model.Space) (spaceTerm source target : Pattern) :
    (totalTheory model space spaceTerm).Step source target ↔
      target ∈ rewriteStepWithPremisesUsing
        (relationEnv model space spaceTerm) language source := by
  rw [totalTheory_step]
  unfold langReducesUsing
  rw [step_iff_rootStep_of_noncontextualRules zero_rules_noncontextual]
  exact rootStep_iff_mem_executor _ _ _

@[simp] private theorem match_query_row
    (spaceTerm pattern template answer : Pattern) :
    matchRelationArgs
        [("pattern", pattern), ("template", template), ("space", spaceTerm)]
        [metavariable "space", metavariable "pattern", metavariable "template",
          metavariable "answer"]
        [spaceTerm, pattern, template, answer] =
      [[("answer", answer)]] := by
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings, metavariable]

@[simp] private theorem match_evaluation_row
    (spaceTerm subject answer : Pattern) :
    matchRelationArgs [("subject", subject), ("space", spaceTerm)]
        [metavariable "space", metavariable "subject", metavariable "answer"]
        [spaceTerm, subject, answer] =
      [[("answer", answer)]] := by
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings, metavariable]

private def queryRowResults (spaceTerm pattern template : Pattern)
    (answers : List Pattern) : List Pattern :=
  ((answers.map fun answer => [spaceTerm, pattern, template, answer]).flatMap
      (fun tuple =>
        (matchRelationArgs
            [("pattern", pattern), ("template", template), ("space", spaceTerm)]
            [metavariable "space", metavariable "pattern", metavariable "template",
              metavariable "answer"] tuple).filterMap
          (fun extension => extension.foldlM
            (init := [("pattern", pattern), ("template", template),
              ("space", spaceTerm)]) fun accumulated entry =>
              match accumulated.find? (fun existing => existing.1 == entry.1) with
              | none => some (entry :: accumulated)
              | some (_, existing) =>
                  if existing = entry.2 then some accumulated else none))).map
      (fun bindings =>
        Pattern.apply "zero-query-answer"
          [match bindings.find? (fun binding => binding.1 == "answer") with
           | some (_, value) => value
           | none => Pattern.fvar "answer"])

private def evaluationRowResults (spaceTerm subject : Pattern)
    (answers : List Pattern) : List Pattern :=
  ((answers.map fun answer => [spaceTerm, subject, answer]).flatMap
      (fun tuple =>
        (matchRelationArgs [("subject", subject), ("space", spaceTerm)]
            [metavariable "space", metavariable "subject", metavariable "answer"]
            tuple).filterMap
          (fun extension => extension.foldlM
            (init := [("subject", subject), ("space", spaceTerm)])
              fun accumulated entry =>
                match accumulated.find? (fun existing => existing.1 == entry.1) with
                | none => some (entry :: accumulated)
                | some (_, existing) =>
                    if existing = entry.2 then some accumulated else none))).map
      (fun bindings =>
        Pattern.apply "zero-evaluate-answer"
          [match bindings.find? (fun binding => binding.1 == "answer") with
           | some (_, value) => value
           | none => Pattern.fvar "answer"])

@[simp] private theorem execute_query_rows
    (spaceTerm pattern template : Pattern) (answers : List Pattern) :
    queryRowResults spaceTerm pattern template answers =
      answers.map fun answer => Pattern.apply "zero-query-answer" [answer] := by
  unfold queryRowResults
  induction answers with
  | nil => rfl
  | cons answer answers inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [match_query_row, inductionHypothesis]
      simp

@[simp] private theorem execute_evaluation_rows
    (spaceTerm subject : Pattern) (answers : List Pattern) :
    evaluationRowResults spaceTerm subject answers =
      answers.map fun answer => Pattern.apply "zero-evaluate-answer" [answer] := by
  unfold evaluationRowResults
  induction answers with
  | nil => rfl
  | cons answer answers inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [match_evaluation_row, inductionHypothesis]
      simp

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The generic executor applied to an authored query request enumerates
exactly the semantic query bag. -/
theorem query_rewrite_bag_adequate (model : Model) (space : model.Space)
    (spaceTerm pattern template : Pattern) :
    (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (queryRequestPattern spaceTerm pattern template) :
      Multiset Pattern) =
      (query model space pattern template).map queryAnswerPattern := by
  simp (config := { maxSteps := 300000 })
    [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, semanticRelationEnv, language,
      definition,
      queryRewrite, evaluationRewrite,
      queryRequestPattern, queryAnswerPattern, evaluationRequestPattern,
      evaluationAnswerPattern, metavariable, matchPatternForRule,
      matchPatternForRuleUsing, applyBindingsForRule,
      applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
      applyBindings]
  change (queryRowResults spaceTerm pattern template
      (query model space pattern template).toList : Multiset Pattern) = _
  rw [execute_query_rows]
  conv_rhs => rw [← Multiset.coe_toList (query model space pattern template)]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The generic executor applied to an authored evaluation request enumerates
exactly the semantic evaluation bag. -/
theorem evaluation_rewrite_bag_adequate (model : Model) (space : model.Space)
    (spaceTerm subject : Pattern) :
    (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (evaluationRequestPattern spaceTerm subject) :
      Multiset Pattern) =
      (evaluateOne model space subject).map evaluationAnswerPattern := by
  simp (config := { maxSteps := 300000 })
    [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, semanticRelationEnv, language,
      definition,
      queryRewrite, evaluationRewrite,
      queryRequestPattern, queryAnswerPattern, evaluationRequestPattern,
      evaluationAnswerPattern, metavariable, matchPatternForRule,
      matchPatternForRuleUsing, applyBindingsForRule,
      applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
      applyBindings]
  change (evaluationRowResults spaceTerm subject
      (evaluateOne model space subject).toList : Multiset Pattern) = _
  rw [execute_evaluation_rows]
  conv_rhs => rw [← Multiset.coe_toList (evaluateOne model space subject)]
  rfl

/-! ## Adequacy of the combined GSLT -/

/-- A public query answer occurs in the semantic bag exactly when the authored
request reduces to that answer in Zero's combined GSLT. -/
theorem totalTheory_query_step_iff (model : Model) (space : model.Space)
    (spaceTerm pattern template answer : Pattern) :
    (totalTheory model space spaceTerm).Step
        (queryRequestPattern spaceTerm pattern template)
        (queryAnswerPattern answer) ↔
      answer ∈ query model space pattern template := by
  rw [totalTheory_step_iff_mem_executor]
  change queryAnswerPattern answer ∈
      (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (queryRequestPattern spaceTerm pattern template) :
          Multiset Pattern) ↔ _
  rw [query_rewrite_bag_adequate]
  simp [queryAnswerPattern]

/-- A public evaluation answer occurs in the query-derived semantic bag
exactly when the authored request reduces to that answer in Zero's combined
GSLT. -/
theorem totalTheory_evaluation_step_iff (model : Model)
    (space : model.Space) (spaceTerm subject answer : Pattern) :
    (totalTheory model space spaceTerm).Step
        (evaluationRequestPattern spaceTerm subject)
        (evaluationAnswerPattern answer) ↔
      answer ∈ evaluateOne model space subject := by
  rw [totalTheory_step_iff_mem_executor]
  change evaluationAnswerPattern answer ∈
      (rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (evaluationRequestPattern spaceTerm subject) :
          Multiset Pattern) ↔ _
  rw [evaluation_rewrite_bag_adequate]
  simp [evaluationAnswerPattern]

/-! ## Certified realization of the authored root

The two entry forms share one realization interface.  Its source observation is
the query-first semantic kernel; its artifact is the occurrence bag emitted by
the generic premise-aware interpreter over the authored five-field language.
The adequacy field is therefore exactly the two theorems above, not a new
semantic relation. -/

/-- A request to one of the two public operations of the authored Zero root. -/
inductive KernelRequest (model : Model) where
  | query (space : model.Space) (spaceTerm pattern template : Pattern)
  | evaluate (space : model.Space) (spaceTerm subject : Pattern)

/-- The semantic occurrence observation named by a Zero kernel request. -/
def semanticAnswers {model : Model} : KernelRequest model → Multiset Pattern
  | .query space _ pattern template =>
      (query model space pattern template).map queryAnswerPattern
  | .evaluate space _ subject =>
      (evaluateOne model space subject).map evaluationAnswerPattern

/-- Execute a request using only the generic interpreter and the authored
five-field root. -/
noncomputable def executeAuthored {model : Model} :
    KernelRequest model → Multiset Pattern
  | .query space spaceTerm pattern template =>
      rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (queryRequestPattern spaceTerm pattern template)
  | .evaluate space spaceTerm subject =>
      rewriteStepWithPremisesUsing (relationEnv model space spaceTerm)
        language (evaluationRequestPattern spaceTerm subject)

/-- **Zero's authored five-field root is a certified realization of its
query-first semantics.**  Query and evaluation are selected by the request;
both are interpreted by the same generic executor and preserve the complete
occurrence bag. -/
noncomputable def authoredRealization (model : Model) :
    SimpleRealization (KernelRequest model) (Multiset Pattern)
      (Multiset Pattern) where
  compile := fun _ request => executeAuthored request
  observeSource := fun _ request => semanticAnswers request
  observeArtifact := fun _ answers => answers
  adequate := by
    intro _ request
    cases request with
    | query space spaceTerm pattern template =>
        exact query_rewrite_bag_adequate model space spaceTerm pattern template
    | evaluate space spaceTerm subject =>
        exact evaluation_rewrite_bag_adequate model space spaceTerm subject

@[simp] theorem authoredRealization_query (model : Model)
    (space : model.Space) (spaceTerm pattern template : Pattern) :
    (authoredRealization model).compile ()
        (.query space spaceTerm pattern template) =
      (query model space pattern template).map queryAnswerPattern :=
  (authoredRealization model).adequate ()
    (.query space spaceTerm pattern template)

@[simp] theorem authoredRealization_evaluate (model : Model)
    (space : model.Space) (spaceTerm subject : Pattern) :
    (authoredRealization model).compile ()
        (.evaluate space spaceTerm subject) =
      (evaluateOne model space subject).map evaluationAnswerPattern :=
  (authoredRealization model).adequate ()
    (.evaluate space spaceTerm subject)

/-- The realization does not collapse the two public operations into one
request constructor. -/
theorem query_request_ne_evaluation_request (model : Model)
    (space : model.Space) (spaceTerm pattern : Pattern) :
    KernelRequest.query space spaceTerm pattern pattern ≠
      KernelRequest.evaluate space spaceTerm pattern := by
  intro equal
  cases equal

end Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
