import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.NativeTypeTheory
import Mettapedia.OSLF.Framework.NativeTypeProofGSLT
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mathlib.Tactic.NormNum

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
open Mettapedia.OSLF.Framework.NativeTypeTheory

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

/-! ## OSLF-derived native types

The semantic relation environment is part of Zero's interpreted reduction
span.  Running the authored five-field language through OSLF therefore yields
spatial request/answer types and behavioral diamonds without adding another
semantic relation.  These views are suitable for proof certificates and
compiler indexes, but their propositional modality intentionally observes
existence rather than occurrence multiplicity. -/

/-- The OSLF reduction span of one interpreted Zero model and named space. -/
noncomputable def nativeSpan (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :
    Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan Pattern :=
  langSpanUsing (relationEnv model space spaceTerm) language

/-- Native inhabitation derived from the interpreted Zero span. -/
noncomputable def nativeSatisfies (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : NativeType → Pattern → Prop :=
  satisfiesOver (nativeSpan model space spaceTerm)

/-- The spatial type of an ordinary equation atom. -/
def equationNativeType : NativeType :=
  .headed "=" [.top, .top]

/-- The spatial type of a public query request. -/
def queryRequestNativeType : NativeType :=
  .headed "zero-query" [.top, .top, .top]

/-- The spatial type of a public query answer. -/
def queryAnswerNativeType : NativeType :=
  .headed "zero-query-answer" [.top]

/-- The spatial type of a public evaluation request. -/
def evaluationRequestNativeType : NativeType :=
  .headed "zero-evaluate" [.top, .top]

/-- The spatial type of a public evaluation answer. -/
def evaluationAnswerNativeType : NativeType :=
  .headed "zero-evaluate-answer" [.top]

/-- The complete spatial signature mechanically generated from Zero's term
grammar. -/
theorem zero_constructorTypes : constructorTypes language =
    [equationNativeType, queryRequestNativeType,
      queryAnswerNativeType, evaluationRequestNativeType,
      evaluationAnswerNativeType] :=
  rfl

@[simp] theorem nativeSatisfies_queryRequest (model : Model)
    (space : model.Space) (spaceTerm pattern template : Pattern) :
    nativeSatisfies model space spaceTerm queryRequestNativeType
      (queryRequestPattern spaceTerm pattern template) := by
  exact ⟨[spaceTerm, pattern, template], rfl, ⟨trivial, ⟨trivial,
    ⟨trivial, trivial⟩⟩⟩⟩

@[simp] theorem nativeSatisfies_evaluationRequest (model : Model)
    (space : model.Space) (spaceTerm subject : Pattern) :
    nativeSatisfies model space spaceTerm evaluationRequestNativeType
      (evaluationRequestPattern spaceTerm subject) := by
  exact ⟨[spaceTerm, subject], rfl, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

/-- The generated query-answer type recognizes exactly the authored answer
constructor. -/
theorem nativeSatisfies_queryAnswer_iff (model : Model)
    (space : model.Space) (spaceTerm target : Pattern) :
    nativeSatisfies model space spaceTerm queryAnswerNativeType target ↔
      ∃ answer, target = queryAnswerPattern answer := by
  constructor
  · rintro ⟨children, shape, inhabited⟩
    cases children with
    | nil => simp [satisfiesAllOver] at inhabited
    | cons answer rest =>
        cases rest with
        | nil => exact ⟨answer, shape⟩
        | cons extra rest => simp [satisfiesAllOver] at inhabited
  · rintro ⟨answer, rfl⟩
    exact ⟨[answer], rfl, ⟨trivial, trivial⟩⟩

/-- The generated evaluation-answer type recognizes exactly the authored
answer constructor. -/
theorem nativeSatisfies_evaluationAnswer_iff (model : Model)
    (space : model.Space) (spaceTerm target : Pattern) :
    nativeSatisfies model space spaceTerm evaluationAnswerNativeType target ↔
      ∃ answer, target = evaluationAnswerPattern answer := by
  constructor
  · rintro ⟨children, shape, inhabited⟩
    cases children with
    | nil => simp [satisfiesAllOver] at inhabited
    | cons answer rest =>
        cases rest with
        | nil => exact ⟨answer, shape⟩
        | cons extra rest => simp [satisfiesAllOver] at inhabited
  · rintro ⟨answer, rfl⟩
    exact ⟨[answer], rfl, ⟨trivial, trivial⟩⟩

/-- **OSLF query adequacy.**  The derived behavioral diamond holds exactly
when the two-line Zero query semantics contains an answer. -/
theorem native_queryDiamond_iff (model : Model) (space : model.Space)
    (spaceTerm pattern template : Pattern) :
    nativeSatisfies model space spaceTerm (.diamond queryAnswerNativeType)
        (queryRequestPattern spaceTerm pattern template) ↔
      ∃ answer, answer ∈ query model space pattern template := by
  change langDiamondUsing (relationEnv model space spaceTerm) language
      (nativeSatisfies model space spaceTerm queryAnswerNativeType)
      (queryRequestPattern spaceTerm pattern template) ↔ _
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨target, step, targetInhabited⟩
    obtain ⟨answer, rfl⟩ :=
      (nativeSatisfies_queryAnswer_iff model space spaceTerm target).mp
        targetInhabited
    exact ⟨answer, (totalTheory_query_step_iff model space spaceTerm pattern
      template answer).mp ((totalTheory_step model space spaceTerm _ _).mpr step)⟩
  · rintro ⟨answer, answerMember⟩
    refine ⟨queryAnswerPattern answer, ?_, ?_⟩
    · exact (totalTheory_step model space spaceTerm _ _).mp
        ((totalTheory_query_step_iff model space spaceTerm pattern template
          answer).mpr answerMember)
    · exact (nativeSatisfies_queryAnswer_iff model space spaceTerm _).mpr
        ⟨answer, rfl⟩

/-- **OSLF evaluation adequacy.**  The derived behavioral diamond holds
exactly when the two-line Zero evaluator contains an answer. -/
theorem native_evaluationDiamond_iff (model : Model) (space : model.Space)
    (spaceTerm subject : Pattern) :
    nativeSatisfies model space spaceTerm
        (.diamond evaluationAnswerNativeType)
        (evaluationRequestPattern spaceTerm subject) ↔
      ∃ answer, answer ∈ evaluateOne model space subject := by
  change langDiamondUsing (relationEnv model space spaceTerm) language
      (nativeSatisfies model space spaceTerm evaluationAnswerNativeType)
      (evaluationRequestPattern spaceTerm subject) ↔ _
  rw [langDiamondUsing_spec]
  constructor
  · rintro ⟨target, step, targetInhabited⟩
    obtain ⟨answer, rfl⟩ :=
      (nativeSatisfies_evaluationAnswer_iff model space spaceTerm target).mp
        targetInhabited
    exact ⟨answer, (totalTheory_evaluation_step_iff model space spaceTerm
      subject answer).mp ((totalTheory_step model space spaceTerm _ _).mpr step)⟩
  · rintro ⟨answer, answerMember⟩
    refine ⟨evaluationAnswerPattern answer, ?_, ?_⟩
    · exact (totalTheory_step model space spaceTerm _ _).mp
        ((totalTheory_evaluation_step_iff model space spaceTerm subject
          answer).mpr answerMember)
    · exact
        (nativeSatisfies_evaluationAnswer_iff model space spaceTerm _).mpr
          ⟨answer, rfl⟩

/-- Inertness makes every evaluation request behaviorally live: it always has
at least one answer edge, even when no equation or grounding capability
understands the subject. -/
theorem native_evaluationDiamond (model : Model) (space : model.Space)
    (spaceTerm subject : Pattern) :
    nativeSatisfies model space spaceTerm
      (.diamond evaluationAnswerNativeType)
      (evaluationRequestPattern spaceTerm subject) := by
  rw [native_evaluationDiamond_iff]
  apply Multiset.exists_mem_of_ne_zero
  by_cases empty : interpretedResults model space subject = 0
  · simp [evaluateOne, empty]
  · simp [evaluateOne, empty]

/-- A finite native-type trace exists for a query request exactly when the
query has a semantic answer.  The certificate retains the reduction edge and
the spatial evidence for its target. -/
theorem query_nativeCertificate_iff (model : Model) (space : model.Space)
    (spaceTerm pattern template : Pattern) :
    Nonempty
        (Certificate (nativeSpan model space spaceTerm)
          (.diamond queryAnswerNativeType)
          (queryRequestPattern spaceTerm pattern template)) ↔
      ∃ answer, answer ∈ query model space pattern template := by
  constructor
  · rintro ⟨certificate⟩
    exact (native_queryDiamond_iff model space spaceTerm pattern template).mp
      certificate.sound
  · intro answerExists
    apply Certificate.complete
    · rfl
    · exact (native_queryDiamond_iff model space spaceTerm pattern template).mpr
        answerExists

/-- A finite native-type trace exists for an evaluation request exactly when
the evaluator has a semantic answer. -/
theorem evaluation_nativeCertificate_iff (model : Model)
    (space : model.Space) (spaceTerm subject : Pattern) :
    Nonempty
        (Certificate (nativeSpan model space spaceTerm)
          (.diamond evaluationAnswerNativeType)
          (evaluationRequestPattern spaceTerm subject)) ↔
      ∃ answer, answer ∈ evaluateOne model space subject := by
  constructor
  · rintro ⟨certificate⟩
    exact (native_evaluationDiamond_iff model space spaceTerm subject).mp
      certificate.sound
  · intro answerExists
    apply Certificate.complete
    · rfl
    · exact (native_evaluationDiamond_iff model space spaceTerm subject).mpr
        answerExists

/-- Every Zero evaluation request has a finite behavioral-spatial trace. -/
theorem evaluation_nativeCertificate (model : Model) (space : model.Space)
    (spaceTerm subject : Pattern) :
    Nonempty
      (Certificate (nativeSpan model space spaceTerm)
        (.diamond evaluationAnswerNativeType)
        (evaluationRequestPattern spaceTerm subject)) := by
  rw [evaluation_nativeCertificate_iff]
  exact (native_evaluationDiamond_iff model space spaceTerm subject).mp
    (native_evaluationDiamond model space spaceTerm subject)

/-! ## Native-type-guided rule planning -/

/-- The two request routes exposed by Zero's generated spatial types. -/
inductive NativeRequestRoute where
  | query
  | evaluate
deriving Repr, DecidableEq

/-- Exact spatial dispatch key for a request route. -/
def NativeRequestRoute.signature : NativeRequestRoute → HeadSignature
  | .query => ⟨"zero-query", 3⟩
  | .evaluate => ⟨"zero-evaluate", 2⟩

@[simp] theorem queryRequestNativeType_signature :
    queryRequestNativeType.headSignature? =
      some NativeRequestRoute.query.signature :=
  rfl

@[simp] theorem evaluationRequestNativeType_signature :
    evaluationRequestNativeType.headSignature? =
      some NativeRequestRoute.evaluate.signature :=
  rfl

/-- Classify only an exact generated request head.  An unrecognized term is
not rejected; the compiler must retain the full rule table for it. -/
def nativeRequestRoute? (pattern : Pattern) : Option NativeRequestRoute :=
  match patternHeadSignature? pattern with
  | some signature =>
      if signature = NativeRequestRoute.query.signature then some .query
      else if signature = NativeRequestRoute.evaluate.signature then some .evaluate
      else none
  | none => none

@[simp] theorem nativeRequestRoute_query (spaceTerm pattern template : Pattern) :
    nativeRequestRoute? (queryRequestPattern spaceTerm pattern template) =
      some .query := by
  simp [nativeRequestRoute?, patternHeadSignature?, queryRequestPattern,
    NativeRequestRoute.signature]

@[simp] theorem nativeRequestRoute_evaluate (spaceTerm subject : Pattern) :
    nativeRequestRoute? (evaluationRequestPattern spaceTerm subject) =
      some .evaluate := by
  simp [nativeRequestRoute?, patternHeadSignature?, evaluationRequestPattern,
    NativeRequestRoute.signature]

/-- Negative canary: result constructors are not accidentally reclassified
as executable requests. -/
@[simp] theorem nativeRequestRoute_queryAnswer (answer : Pattern) :
    nativeRequestRoute? (queryAnswerPattern answer) = none := by
  simp [nativeRequestRoute?, patternHeadSignature?, queryAnswerPattern,
    NativeRequestRoute.signature]

/-- Negative canary: arbitrary applications retain fallback behavior. -/
example : nativeRequestRoute? (.apply "unknown" []) = none := by
  decide

/-- Rules whose authored left-hand side has one exact native spatial key. -/
def rulesForNativeSignature (signature : HeadSignature) : List RewriteRule :=
  language.rewrites.filter fun rule =>
    decide (patternHeadSignature? rule.left = some signature)

/-- Candidate table selected by one recognized native request type. -/
def nativeCandidateRules (route : NativeRequestRoute) : List RewriteRule :=
  rulesForNativeSignature route.signature

@[simp] theorem nativeCandidateRules_query :
    nativeCandidateRules .query = [queryRewrite] := by
  simp [nativeCandidateRules, rulesForNativeSignature, language_rewrites,
    queryRewrite, evaluationRewrite, queryRequestPattern,
    evaluationRequestPattern, patternHeadSignature?, NativeRequestRoute.signature]

@[simp] theorem nativeCandidateRules_evaluate :
    nativeCandidateRules .evaluate = [evaluationRewrite] := by
  simp [nativeCandidateRules, rulesForNativeSignature, language_rewrites,
    queryRewrite, evaluationRewrite, queryRequestPattern,
    evaluationRequestPattern, patternHeadSignature?, NativeRequestRoute.signature]

/-- Fail-closed rule planning: recognized native types narrow the table;
everything else keeps the complete authored rule inventory. -/
def nativePlannedRules (source : Pattern) : List RewriteRule :=
  match nativeRequestRoute? source with
  | some route => nativeCandidateRules route
  | none => language.rewrites

@[simp] theorem nativePlannedRules_query (spaceTerm pattern template : Pattern) :
    nativePlannedRules (queryRequestPattern spaceTerm pattern template) =
      [queryRewrite] := by
  simp [nativePlannedRules]

@[simp] theorem nativePlannedRules_evaluate (spaceTerm subject : Pattern) :
    nativePlannedRules (evaluationRequestPattern spaceTerm subject) =
      [evaluationRewrite] := by
  simp [nativePlannedRules]

@[simp] theorem nativePlannedRules_unknown :
    nativePlannedRules (.apply "unknown" []) = language.rewrites := by
  simp [nativePlannedRules, nativeRequestRoute?, patternHeadSignature?,
    NativeRequestRoute.signature]

/-- Execute the plan selected from Zero's generated spatial native type.  The
ordinary generic engine remains the fallback for every unclassified term. -/
def executeNativePlanned (relEnv : RelationEnv) (source : Pattern) :
    List Pattern :=
  (nativePlannedRules source).flatMap fun rule =>
    applyRuleWithPremisesUsing relEnv language rule source

/-- The query head index removes only the impossible evaluation rule. -/
theorem executeNativePlanned_query (relEnv : RelationEnv)
    (spaceTerm pattern template : Pattern) :
    executeNativePlanned relEnv
        (queryRequestPattern spaceTerm pattern template) =
      rewriteStepWithPremisesUsing relEnv language
        (queryRequestPattern spaceTerm pattern template) := by
  unfold executeNativePlanned rewriteStepWithPremisesUsing
  rw [nativePlannedRules_query]
  simp (config := { maxSteps := 100000 })
    [applyRuleWithPremisesUsing, language_rewrites, evaluationRewrite,
      evaluationRequestPattern, queryRequestPattern, matchPatternForRule,
      matchPatternForRuleUsing, matchPattern]

/-- The evaluation head index removes only the impossible query rule. -/
theorem executeNativePlanned_evaluate (relEnv : RelationEnv)
    (spaceTerm subject : Pattern) :
    executeNativePlanned relEnv
        (evaluationRequestPattern spaceTerm subject) =
      rewriteStepWithPremisesUsing relEnv language
        (evaluationRequestPattern spaceTerm subject) := by
  unfold executeNativePlanned rewriteStepWithPremisesUsing
  rw [nativePlannedRules_evaluate]
  simp (config := { maxSteps := 100000 })
    [applyRuleWithPremisesUsing, language_rewrites, queryRewrite,
      queryRequestPattern, evaluationRequestPattern, matchPatternForRule,
      matchPatternForRuleUsing, matchPattern]

/-- The fallback path is definitionally the complete generic engine. -/
theorem executeNativePlanned_unknown (relEnv : RelationEnv) :
    executeNativePlanned relEnv (.apply "unknown" []) =
      rewriteStepWithPremisesUsing relEnv language (.apply "unknown" []) := by
  simp [executeNativePlanned, rewriteStepWithPremisesUsing]

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

/-- Execute the same request through the OSLF-native spatial index.  Only the
impossible root rule is removed; every untyped entry point still has the
generic fallback in `executeNativePlanned`. -/
noncomputable def executeAuthoredNativePlanned {model : Model} :
    KernelRequest model → Multiset Pattern
  | .query space spaceTerm pattern template =>
      executeNativePlanned (relationEnv model space spaceTerm)
        (queryRequestPattern spaceTerm pattern template)
  | .evaluate space spaceTerm subject =>
      executeNativePlanned (relationEnv model space spaceTerm)
        (evaluationRequestPattern spaceTerm subject)

/-- The native spatial plan is exactly the generic authored executor on every
typed Zero request, including order and duplicate occurrences. -/
theorem executeAuthoredNativePlanned_eq {model : Model}
    (request : KernelRequest model) :
    executeAuthoredNativePlanned request = executeAuthored request := by
  cases request with
  | query space spaceTerm pattern template =>
      exact congrArg (fun results : List Pattern => (results : Multiset Pattern))
        (executeNativePlanned_query
          (relationEnv model space spaceTerm) spaceTerm pattern template)
  | evaluate space spaceTerm subject =>
      exact congrArg (fun results : List Pattern => (results : Multiset Pattern))
        (executeNativePlanned_evaluate
          (relationEnv model space spaceTerm) spaceTerm subject)

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

/-- The OSLF-native indexed executor is a second certified realization of the
same exact occurrence-bag semantics. -/
noncomputable def nativePlannedRealization (model : Model) :
    SimpleRealization (KernelRequest model) (Multiset Pattern)
      (Multiset Pattern) where
  compile := fun _ request => executeAuthoredNativePlanned request
  observeSource := fun _ request => semanticAnswers request
  observeArtifact := fun _ answers => answers
  adequate := by
    intro _ request
    rw [executeAuthoredNativePlanned_eq]
    exact (authoredRealization model).adequate () request

/-- Both execution routes agree before any observation quotient. -/
theorem nativePlanned_eq_authored (model : Model)
    (request : KernelRequest model) :
    (nativePlannedRealization model).compile () request =
      (authoredRealization model).compile () request :=
  executeAuthoredNativePlanned_eq request

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

/-! ## ProofGSLT presentation of Zero's generated native judgments

The presentation below is a proof layer over the existing authored Zero
language.  It does not redefine Zero reduction.  Spatial judgments are
generated from Zero's constructors; behavioral judgments require an explicit
query/evaluation-row premise.  Consequently a native checker may replay the
article without treating a relation implementation as an axiom. -/

namespace NativeProof

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.OSLF.Framework.NativeTypeProofGSLT

def topJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeTop" [term]

def equationJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeEquation" [term]

def queryRequestJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeQueryRequest" [term]

def queryAnswerJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeQueryAnswer" [term]

def evaluationRequestJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeEvaluationRequest" [term]

def evaluationAnswerJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeEvaluationAnswer" [term]

def queryLiveJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeQueryLive" [term]

def evaluationLiveJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeEvaluationLive" [term]

def unsupportedJ (term : Pattern) : Pattern :=
  .apply "ZeroNativeUnsupported" [term]

def queryRowJ (spaceTerm pattern template answer : Pattern) : Pattern :=
  .apply "ZeroQueryRow" [spaceTerm, pattern, template, answer]

def evaluationRowJ (spaceTerm subject answer : Pattern) : Pattern :=
  .apply "ZeroEvaluationRow" [spaceTerm, subject, answer]

private def ruleId (name : String) : RuleId := ⟨name⟩

private def schema (name : String) (metavariables : List (String × Nat))
    (premises : List Pattern) (conclusion : Pattern) : RuleSchema :=
  { id := ruleId name, metavariables, premises, conclusion }

def topRule : RuleSchema :=
  schema "zero-native-top" [("term", 0)] [] (topJ (.fvar "term"))

def equationRule : RuleSchema :=
  schema "zero-native-equation" [("left", 0), ("right", 0)] []
    (equationJ (.apply "=" [.fvar "left", .fvar "right"]))

def queryRequestRule : RuleSchema :=
  schema "zero-native-query-request"
    [("space", 0), ("pattern", 0), ("template", 0)] []
    (queryRequestJ
      (queryRequestPattern (.fvar "space") (.fvar "pattern")
        (.fvar "template")))

def queryAnswerRule : RuleSchema :=
  schema "zero-native-query-answer" [("answer", 0)] []
    (queryAnswerJ (queryAnswerPattern (.fvar "answer")))

def evaluationRequestRule : RuleSchema :=
  schema "zero-native-evaluation-request"
    [("space", 0), ("subject", 0)] []
    (evaluationRequestJ
      (evaluationRequestPattern (.fvar "space") (.fvar "subject")))

def evaluationAnswerRule : RuleSchema :=
  schema "zero-native-evaluation-answer" [("answer", 0)] []
    (evaluationAnswerJ (evaluationAnswerPattern (.fvar "answer")))

/-- Behavioral liveness is justified by a particular public query row. -/
def queryLiveRule : RuleSchema :=
  schema "zero-native-query-live"
    [("space", 0), ("pattern", 0), ("template", 0), ("answer", 0)]
    [queryRowJ (.fvar "space") (.fvar "pattern") (.fvar "template")
      (.fvar "answer")]
    (queryLiveJ
      (queryRequestPattern (.fvar "space") (.fvar "pattern")
        (.fvar "template")))

/-- Behavioral liveness is justified by a particular evaluation row. -/
def evaluationLiveRule : RuleSchema :=
  schema "zero-native-evaluation-live"
    [("space", 0), ("subject", 0), ("answer", 0)]
    [evaluationRowJ (.fvar "space") (.fvar "subject") (.fvar "answer")]
    (evaluationLiveJ
      (evaluationRequestPattern (.fvar "space") (.fvar "subject")))

def rules : List RuleSchema :=
  [topRule, equationRule, queryRequestRule, queryAnswerRule,
    evaluationRequestRule, evaluationAnswerRule, queryLiveRule,
    evaluationLiveRule]

/-- The native proof calculus is authored over the exact five-field Zero
root.  `ZeroNativeUnsupported` is declared but intentionally has no rule, so
an unsupported native former fails closed rather than becoming refutation. -/
def definition : CalculusLanguageDef :=
  { toLanguageDef := language
    judgments :=
      [ { head := "ZeroNativeTop", arity := 1 },
        { head := "ZeroNativeEquation", arity := 1 },
        { head := "ZeroNativeQueryRequest", arity := 1 },
        { head := "ZeroNativeQueryAnswer", arity := 1 },
        { head := "ZeroNativeEvaluationRequest", arity := 1 },
        { head := "ZeroNativeEvaluationAnswer", arity := 1 },
        { head := "ZeroNativeQueryLive", arity := 1 },
        { head := "ZeroNativeEvaluationLive", arity := 1 },
        { head := "ZeroNativeUnsupported", arity := 1 },
        { head := "ZeroQueryRow", arity := 4 },
        { head := "ZeroEvaluationRow", arity := 3 } ]
    rules }

def presentation : Presentation := definition.toNested

private theorem root_terms : language.terms =
    [equationConstructor, queryRequestConstructor, queryAnswerConstructor,
      evaluationRequestConstructor, evaluationAnswerConstructor] :=
  rfl

@[simp] private theorem equationConstructor_shape :
    equationConstructor.label = "=" ∧ equationConstructor.params.length = 2 :=
  by decide

@[simp] private theorem queryRequestConstructor_shape :
    queryRequestConstructor.label = "zero-query" ∧
      queryRequestConstructor.params.length = 3 :=
  by decide

@[simp] private theorem queryAnswerConstructor_shape :
    queryAnswerConstructor.label = "zero-query-answer" ∧
      queryAnswerConstructor.params.length = 1 :=
  by decide

@[simp] private theorem evaluationRequestConstructor_shape :
    evaluationRequestConstructor.label = "zero-evaluate" ∧
      evaluationRequestConstructor.params.length = 2 :=
  by decide

@[simp] private theorem evaluationAnswerConstructor_shape :
    evaluationAnswerConstructor.label = "zero-evaluate-answer" ∧
      evaluationAnswerConstructor.params.length = 1 :=
  by decide

theorem presentation_valid : presentation.isValidV2 = true := by
  have rootValid : presentation.language.validate = [] := by
    simpa [presentation, definition] using language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [rootValid]
  simp [presentation, definition, rules, topRule, equationRule,
    queryRequestRule, queryAnswerRule, evaluationRequestRule,
    evaluationAnswerRule, queryLiveRule, evaluationLiveRule, schema,
    ruleId, topJ, equationJ, queryRequestJ, queryAnswerJ,
    evaluationRequestJ, evaluationAnswerJ, queryLiveJ, evaluationLiveJ,
    queryRowJ, evaluationRowJ, queryRequestPattern, queryAnswerPattern,
    evaluationRequestPattern, evaluationAnswerPattern,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, List.eraseDups,
    List.eraseDupsBy, root_terms, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead]
  norm_num [List.eraseDupsBy.loop]
  decide

def checked : ValidatedPresentation := ⟨presentation, presentation_valid⟩

/-- Proof syntax for the native fragment generated and used by Zero.  Native
formers outside this finite fragment map to a declared judgment with no rules,
so native replay fails closed. -/
noncomputable def encodeClaim (claim : Claim) : Pattern := by
  classical
  exact
    if claim.nativeType = .top then topJ claim.term
    else if claim.nativeType = equationNativeType then equationJ claim.term
    else if claim.nativeType = queryRequestNativeType then queryRequestJ claim.term
    else if claim.nativeType = queryAnswerNativeType then queryAnswerJ claim.term
    else if claim.nativeType = evaluationRequestNativeType then
      evaluationRequestJ claim.term
    else if claim.nativeType = evaluationAnswerNativeType then
      evaluationAnswerJ claim.term
    else if claim.nativeType = .diamond queryAnswerNativeType then
      queryLiveJ claim.term
    else if claim.nativeType = .diamond evaluationAnswerNativeType then
      evaluationLiveJ claim.term
    else unsupportedJ claim.term

/-- Semantic interpretation of every judgment exposed by the presentation.
Row judgments denote occurrence membership in the exact semantic model; the
other judgments denote OSLF-native inhabitation over the same interpreted
span. -/
noncomputable def judgmentMeaning (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : Pattern → Prop
  | .apply "ZeroNativeTop" [term] =>
      nativeSatisfies model space spaceTerm .top term
  | .apply "ZeroNativeEquation" [term] =>
      nativeSatisfies model space spaceTerm equationNativeType term
  | .apply "ZeroNativeQueryRequest" [term] =>
      nativeSatisfies model space spaceTerm queryRequestNativeType term
  | .apply "ZeroNativeQueryAnswer" [term] =>
      nativeSatisfies model space spaceTerm queryAnswerNativeType term
  | .apply "ZeroNativeEvaluationRequest" [term] =>
      nativeSatisfies model space spaceTerm evaluationRequestNativeType term
  | .apply "ZeroNativeEvaluationAnswer" [term] =>
      nativeSatisfies model space spaceTerm evaluationAnswerNativeType term
  | .apply "ZeroNativeQueryLive" [term] =>
      nativeSatisfies model space spaceTerm (.diamond queryAnswerNativeType) term
  | .apply "ZeroNativeEvaluationLive" [term] =>
      nativeSatisfies model space spaceTerm
        (.diamond evaluationAnswerNativeType) term
  | .apply "ZeroQueryRow" [candidateSpace, pattern, template, answer] =>
      candidateSpace = spaceTerm ∧ answer ∈ query model space pattern template
  | .apply "ZeroEvaluationRow" [candidateSpace, subject, answer] =>
      candidateSpace = spaceTerm ∧ answer ∈ evaluateOne model space subject
  | _ => False

/-- The proof encoding never changes the meaning of a supported native claim;
the unsupported branch has no semantic inhabitants in this presentation. -/
theorem encodeClaim_sound (model : Model) (space : model.Space)
    (spaceTerm : Pattern) (claim : Claim)
    (evidence : judgmentMeaning model space spaceTerm (encodeClaim claim)) :
    claim.Meaning (nativeSpan model space spaceTerm) := by
  classical
  rcases claim with ⟨term, nativeType⟩
  simp only [encodeClaim] at evidence
  split_ifs at evidence with htop hequation hqueryRequest hqueryAnswer
      hevaluationRequest hevaluationAnswer hqueryLive hevaluationLive
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, topJ] using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, equationJ] using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, queryRequestJ]
      using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, queryAnswerJ]
      using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies,
      evaluationRequestJ] using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies,
      evaluationAnswerJ] using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, queryLiveJ]
      using evidence
  · subst nativeType
    simpa [judgmentMeaning, Claim.Meaning, nativeSatisfies, evaluationLiveJ]
      using evidence
  · simp [judgmentMeaning, unsupportedJ] at evidence

private theorem arguments_one {name : String} {arguments : List Pattern}
    (valid : argumentsValidAt [(name, 0)] arguments = true) :
    ∃ first, arguments = [first] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp [argumentsValidAt] at valid

private theorem arguments_two {firstName secondName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0)] arguments = true) :
    ∃ first second, arguments = [first, second] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp [argumentsValidAt] at valid

private theorem arguments_three {firstName secondName thirdName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0)] arguments = true) :
    ∃ first second third, arguments = [first, second, third] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => exact ⟨first, second, third, rfl⟩
              | cons fourth rest => simp [argumentsValidAt] at valid

private theorem arguments_four
    {firstName secondName thirdName fourthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0)]
      arguments = true) :
    ∃ first second third fourth,
      arguments = [first, second, third, fourth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => exact ⟨first, second, third, fourth, rfl⟩
                  | cons fifth rest => simp [argumentsValidAt] at valid

private theorem rule_mem_of_lookup {ruleInstance : RuleInstance}
    {rule : RuleSchema}
    (lookup : checked.1.lookupRule? ruleInstance.ruleId = some rule) :
    rule ∈ rules := by
  unfold Presentation.lookupRule? at lookup
  simpa [checked, presentation, definition] using
    List.mem_of_find?_eq_some lookup

/-- Every admitted native-proof rule preserves the exact Zero/OSLF meaning.
The two behavioral rules consume no semantic oracle: their sole premise is a
row occurrence whose meaning is supplied by the open article context. -/
theorem rule_application_sound (model : Model) (space : model.Space)
    (spaceTerm : Pattern) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication checked ruleInstance premises conclusion)
    (premisesSound : ∀ premise ∈ premises,
      judgmentMeaning model space spaceTerm premise) :
    judgmentMeaning model space spaceTerm conclusion := by
  rcases ruleInstance with ⟨instanceId, arguments⟩
  have instantiated := instantiateRule?_eq_some_iff_application.mpr application
  rcases application with
    ⟨rule, lookup, argumentsValid, sideConditionsValid,
      premisesInstantiate, conclusionInstantiates⟩
  have membership : rule ∈ rules := rule_mem_of_lookup lookup
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨term, rfl⟩ := arguments_one argumentsValid
    change argumentsValidAt [("term", 0)] [term] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [term] } =
        some ([], topJ term) := by
      simp [instantiateRule?, lookup, argumentsValid,
        topRule, schema, topJ, instantiateSchemas?, instantiateSchemasAt?,
        instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    simp [judgmentMeaning, topJ, nativeSatisfies, satisfiesOver]
  · obtain ⟨left, right, rfl⟩ := arguments_two argumentsValid
    change argumentsValidAt [("left", 0), ("right", 0)] [left, right] = true
      at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [left, right] } =
        some ([], equationJ (.apply "=" [left, right])) := by
      simp [instantiateRule?, lookup, argumentsValid,
        equationRule, schema, equationJ, instantiateSchemas?,
        instantiateSchemasAt?, instantiateSchema?, instantiateSchemaAt?,
        lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    change nativeSatisfies model space spaceTerm equationNativeType
      (.apply "=" [left, right])
    exact ⟨[left, right], rfl, ⟨trivial, ⟨trivial, trivial⟩⟩⟩
  · obtain ⟨requestSpace, pattern, template, rfl⟩ :=
      arguments_three argumentsValid
    change argumentsValidAt
      [("space", 0), ("pattern", 0), ("template", 0)]
      [requestSpace, pattern, template] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [requestSpace, pattern, template] } =
        some ([], queryRequestJ
          (queryRequestPattern requestSpace pattern template)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        queryRequestRule, schema, queryRequestJ, queryRequestPattern,
        instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
        instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    change nativeSatisfies model space spaceTerm queryRequestNativeType
      (queryRequestPattern requestSpace pattern template)
    exact ⟨[requestSpace, pattern, template], rfl,
      ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩⟩
  · obtain ⟨answer, rfl⟩ := arguments_one argumentsValid
    change argumentsValidAt [("answer", 0)] [answer] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [answer] } =
        some ([], queryAnswerJ (queryAnswerPattern answer)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        queryAnswerRule, schema, queryAnswerJ, queryAnswerPattern,
        instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
        instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    change nativeSatisfies model space spaceTerm queryAnswerNativeType
      (queryAnswerPattern answer)
    exact (nativeSatisfies_queryAnswer_iff model space spaceTerm _).mpr
      ⟨answer, rfl⟩
  · obtain ⟨requestSpace, subject, rfl⟩ := arguments_two argumentsValid
    change argumentsValidAt [("space", 0), ("subject", 0)]
      [requestSpace, subject] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [requestSpace, subject] } =
        some ([], evaluationRequestJ
          (evaluationRequestPattern requestSpace subject)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        evaluationRequestRule, schema, evaluationRequestJ,
        evaluationRequestPattern, instantiateSchemas?, instantiateSchemasAt?,
        instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    change nativeSatisfies model space spaceTerm evaluationRequestNativeType
      (evaluationRequestPattern requestSpace subject)
    exact ⟨[requestSpace, subject], rfl,
      ⟨trivial, ⟨trivial, trivial⟩⟩⟩
  · obtain ⟨answer, rfl⟩ := arguments_one argumentsValid
    change argumentsValidAt [("answer", 0)] [answer] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [answer] } =
        some ([], evaluationAnswerJ (evaluationAnswerPattern answer)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        evaluationAnswerRule, schema, evaluationAnswerJ,
        evaluationAnswerPattern, instantiateSchemas?, instantiateSchemasAt?,
        instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    change nativeSatisfies model space spaceTerm evaluationAnswerNativeType
      (evaluationAnswerPattern answer)
    exact (nativeSatisfies_evaluationAnswer_iff model space spaceTerm _).mpr
      ⟨answer, rfl⟩
  · obtain ⟨requestSpace, pattern, template, answer, rfl⟩ :=
      arguments_four argumentsValid
    change argumentsValidAt
      [("space", 0), ("pattern", 0), ("template", 0), ("answer", 0)]
      [requestSpace, pattern, template, answer] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId,
          arguments := [requestSpace, pattern, template, answer] } =
        some ([queryRowJ requestSpace pattern template answer],
          queryLiveJ (queryRequestPattern requestSpace pattern template)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        queryLiveRule, schema, queryRowJ, queryLiveJ, queryRequestPattern,
        instantiateSchemas?, instantiateSchemasAt?, instantiateSchema?,
        instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    have row := premisesSound
      (queryRowJ requestSpace pattern template answer) (by simp)
    simp [judgmentMeaning, queryRowJ] at row
    change nativeSatisfies model space spaceTerm
      (.diamond queryAnswerNativeType)
      (queryRequestPattern requestSpace pattern template)
    rw [row.1]
    exact (native_queryDiamond_iff model space spaceTerm pattern template).mpr
      ⟨answer, row.2⟩
  · obtain ⟨requestSpace, subject, answer, rfl⟩ :=
      arguments_three argumentsValid
    change argumentsValidAt
      [("space", 0), ("subject", 0), ("answer", 0)]
      [requestSpace, subject, answer] = true at argumentsValid
    have calculated : instantiateRule? checked
        { ruleId := instanceId, arguments := [requestSpace, subject, answer] } =
        some ([evaluationRowJ requestSpace subject answer],
          evaluationLiveJ (evaluationRequestPattern requestSpace subject)) := by
      simp [instantiateRule?, lookup, argumentsValid,
        evaluationLiveRule, schema, evaluationRowJ, evaluationLiveJ,
        evaluationRequestPattern, instantiateSchemas?, instantiateSchemasAt?,
        instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?]
    have outputs := Option.some.inj (instantiated.symm.trans calculated)
    rcases Prod.mk.inj outputs with ⟨premisesEq, conclusionEq⟩
    subst premises
    subst conclusion
    have row := premisesSound
      (evaluationRowJ requestSpace subject answer) (by simp)
    simp [judgmentMeaning, evaluationRowJ] at row
    change nativeSatisfies model space spaceTerm
      (.diamond evaluationAnswerNativeType)
      (evaluationRequestPattern requestSpace subject)
    rw [row.1]
    exact (native_evaluationDiamond_iff model space spaceTerm subject).mpr
      ⟨answer, row.2⟩

/-- The admitted Zero native presentation is adequate for the interpreted
OSLF span.  Open premise occurrences retain their semantic obligations; only
locally sound rule applications are composed by ProofGSLT. -/
noncomputable def openAdequacy (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :
    OpenPresentationAdequacy (nativeSpan model space spaceTerm) checked where
  encode := encodeClaim
  premiseMeaning := judgmentMeaning model space spaceTerm
  derivation_sound := by
    intro context claim contextSound derivationExists
    obtain ⟨derivation⟩ := derivationExists
    apply encodeClaim_sound model space spaceTerm claim
    exact OpenDerivation.sound_of_ruleApplications
      (judgmentMeaning model space spaceTerm)
      (rule_application_sound model space spaceTerm)
      contextSound derivation

/-- Zero's MIK semantic authority for OSLF-native claims.  It is the generic
open `WireArticle` authority specialized by the adequacy theorem above, not a
second article checker. -/
noncomputable def semanticAuthority {AuthorityId : Type}
    (authorityId : AuthorityId) (model : Model) (space : model.Space)
    (spaceTerm : Pattern) :=
  openWireAuthority authorityId (openAdequacy model space spaceTerm)

/-- The concrete NIK obligation for Zero: native acceptance must lower to an
open article replayed by `semanticAuthority`. -/
abbrev CheckedNativeLowering {AuthorityId : Type}
    (authorityId : AuthorityId) (model : Model) (space : model.Space)
    (spaceTerm : Pattern) (NativeEvidence : Type) :=
  OpenNativeCheckedLowering authorityId
    (openAdequacy model space spaceTerm) NativeEvidence

/-- Any concrete Zero NIK satisfying the replay obligation preserves the
OSLF-native claim once its explicit row/capability premises are discharged. -/
theorem CheckedNativeLowering.satisfies
    {AuthorityId : Type} {authorityId : AuthorityId}
    {model : Model} {space : model.Space} {spaceTerm : Pattern}
    {NativeEvidence : Type}
    (lowering : CheckedNativeLowering authorityId model space spaceTerm
      NativeEvidence)
    {claim : OpenClaim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true)
    (premisesValid : ∀ premise ∈ claim.context,
      judgmentMeaning model space spaceTerm premise) :
    nativeSatisfies model space spaceTerm claim.claim.nativeType
      claim.claim.term :=
  OpenNativeCheckedLowering.satisfies lowering accepted premisesValid

/-! ### Executable positive and negative article canaries -/

def sampleSpaceTerm : Pattern := .apply "zero-native-sample-space" []
def samplePattern : Pattern := .apply "zero-native-sample-pattern" []
def sampleTemplate : Pattern := .apply "zero-native-sample-template" []
def sampleAnswer : Pattern := .apply "zero-native-sample-answer" []

def sampleClaim : Claim :=
  { term := queryRequestPattern sampleSpaceTerm samplePattern sampleTemplate
    nativeType := .diamond queryAnswerNativeType }

def sampleOpenClaim : OpenClaim :=
  { context := [queryRowJ sampleSpaceTerm samplePattern sampleTemplate sampleAnswer]
    claim := sampleClaim }

def sampleRuleInstance : RuleInstance :=
  { ruleId := ruleId "zero-native-query-live"
    arguments := [sampleSpaceTerm, samplePattern, sampleTemplate, sampleAnswer] }

theorem sample_rule_instantiates :
    instantiateRule? checked sampleRuleInstance =
      some
        ([queryRowJ sampleSpaceTerm samplePattern sampleTemplate sampleAnswer],
          queryLiveJ
            (queryRequestPattern sampleSpaceTerm samplePattern sampleTemplate)) := by
  simp [instantiateRule?, checked, presentation, definition, rules,
    Presentation.lookupRule?, topRule, equationRule, queryRequestRule,
    queryAnswerRule, evaluationRequestRule, evaluationAnswerRule,
    queryLiveRule, evaluationLiveRule, schema, ruleId, sampleRuleInstance,
    sampleSpaceTerm, samplePattern, sampleTemplate, sampleAnswer, queryRowJ,
    queryLiveJ, queryRequestPattern, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchemas?, instantiateSchemasAt?,
    instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

def sampleNode : OpenDAGNode :=
  { id := 0
    ruleInstance := sampleRuleInstance
    children := [.premise 0] }

noncomputable def sampleArticle : WireArticle :=
  { version := wireArticleVersion
    nodes := [sampleNode]
    rootId := 0
    target := encodeClaim sampleClaim }

noncomputable def sampleWrongPremiseArticle : WireArticle :=
  { sampleArticle with
    nodes := [{ sampleNode with children := [.premise 1] }] }

/-- A one-row open article is accepted by the same generic chronological DAG
checker used at the MIK boundary. -/
theorem sample_article_accepted {AuthorityId : Type}
    (authorityId : AuthorityId) (model : Model) (space : model.Space) :
    (semanticAuthority authorityId model space sampleSpaceTerm).check
      sampleOpenClaim sampleArticle = true := by
  simp [semanticAuthority, openWireAuthority_check, sampleArticle,
    openAdequacy, sampleOpenClaim, sampleClaim, encodeClaim,
    equationNativeType, queryRequestNativeType, queryAnswerNativeType,
    evaluationRequestNativeType, evaluationAnswerNativeType,
    checkOpenDAGBlocks,
    expandOpenDAGBlocks?, checkOpenDAGBlocks?, checkOpenDAGNodes?,
    checkOpenDAGNode?, resolveOpenDAGChildren?, resolveOpenDAGReference?,
    findOpenDAGEntry?, sampleNode, sample_rule_instantiates]

/-- Changing the sole premise reference to an out-of-range occurrence is
rejected before semantic interpretation. -/
theorem sample_wrong_premise_rejected {AuthorityId : Type}
    (authorityId : AuthorityId) (model : Model) (space : model.Space) :
    (semanticAuthority authorityId model space sampleSpaceTerm).check
      sampleOpenClaim sampleWrongPremiseArticle = false := by
  simp [semanticAuthority, openWireAuthority_check, sampleWrongPremiseArticle,
    sampleArticle, openAdequacy, sampleOpenClaim, sampleClaim, encodeClaim,
    equationNativeType, queryRequestNativeType, queryAnswerNativeType,
    evaluationRequestNativeType, evaluationAnswerNativeType,
    checkOpenDAGBlocks, expandOpenDAGBlocks?, checkOpenDAGBlocks?,
    checkOpenDAGNodes?, checkOpenDAGNode?, resolveOpenDAGChildren?,
    resolveOpenDAGReference?, findOpenDAGEntry?, sampleNode,
    sample_rule_instantiates]

/-- Once the sample row is true in a model, accepted MIK evidence entails the
corresponding OSLF behavioral type. -/
theorem sample_article_semantic (model : Model) (space : model.Space)
    (row : sampleAnswer ∈ query model space samplePattern sampleTemplate) :
    nativeSatisfies model space sampleSpaceTerm
      (.diamond queryAnswerNativeType)
      (queryRequestPattern sampleSpaceTerm samplePattern sampleTemplate) := by
  have meaning :=
    (semanticAuthority "zero-native-proof-v1" model space sampleSpaceTerm).sound
      (sample_article_accepted "zero-native-proof-v1" model space)
  apply meaning
  intro premise premiseMember
  simp [sampleOpenClaim] at premiseMember
  subst premise
  change sampleSpaceTerm = sampleSpaceTerm ∧
    sampleAnswer ∈ query model space samplePattern sampleTemplate
  exact ⟨rfl, row⟩

end NativeProof

end Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
