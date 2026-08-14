import Mettapedia.Languages.MeTTa.Prime.LanguageDef
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Adequacy of Prime's authored five-field rewrites

`Prime.Language` gives the interacting semantic GSLT.  `Prime.LanguageDef`
gives the serializable five-field root.  This module joins them at the generic
MeTTaIL executor.

Every theorem below is explicitly indexed by `QueryFirstModel`: it calibrates
today's authored presentation against today's query-first point.  It is not a law
of every model in Prime's operational specification region.

For every semantic result occurrence, the authored rules expose both routes:

* the direct query-derived Zero evaluation step; and
* the three-step Prime route through a revision-keyed Need request, a causally
  encoded answer receipt, and return to the same extensional observation.

The relation environment below is generated from the semantic evaluator.  It
does not introduce a second evaluation relation: `PrimeNeed` enumerates the
same multiset as `MeTTaZero.evaluateOne`, adding one selected finite cause per
answer value.  Result occurrences remain explicit, but the current receipt
encoding does not identify which equal source occurrence supplied one.
-/

namespace Mettapedia.Languages.MeTTa.Prime.LanguageDefAdequacy

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## Encoding causal receipts -/

/-- A semantic Need key encoded with an explicit representation of revisions. -/
def encodeNeedKey {model : Model} (revisionTerm : model.Revision → Pattern)
    (key : NeedKey model) : Pattern :=
  .apply "prime-need-key" [revisionTerm key.1, key.2]

/-- Every language-level dependency has a constructor in the five-field root. -/
def encodeDependency {model : QueryFirstModel}
    (revisionTerm : model.Revision → Pattern) : Dependency model → Pattern
  | .request key =>
      .apply "prime-request-dependency"
        [encodeNeedKey (model := model.toPrimeModel) revisionTerm key]
  | .spaceAtom key atom =>
      .apply "prime-space-atom-dependency"
        [encodeNeedKey (model := model.toPrimeModel) revisionTerm key, atom]
  | .capability key result =>
      .apply "prime-capability-dependency"
        [encodeNeedKey (model := model.toPrimeModel) revisionTerm key, result]
  | .inert key =>
      .apply "prime-inert-dependency"
        [encodeNeedKey (model := model.toPrimeModel) revisionTerm key]

/-- Encode the root of the finite causal receipt carried by one answer. -/
def encodeReceipt {model : QueryFirstModel} {space : model.Space}
    {subject result : Pattern} (revisionTerm : model.Revision → Pattern)
    (cause : Cause model space subject result) : Pattern :=
  .apply "prime-receipt" [encodeDependency revisionTerm cause.dependency]

/-- Select one finite cause for each semantic result value.  Equal result
occurrences intentionally select the same value-level receipt.  The failure
branch is never emitted by `semanticNeedAnswers`; retaining it makes the
encoder total. -/
noncomputable def receiptFor (model : QueryFirstModel) (space : model.Space)
    (revisionTerm : model.Revision → Pattern) (subject result : Pattern) :
    Pattern :=
  if member : result ∈ MeTTaZero.evaluateOne model.zero space subject then
    encodeReceipt revisionTerm
      (exists_cause_of_mem_evaluateOne model space subject result member).some
  else
    .apply "prime-receipt" [result]

/-- Every receipt that can actually be emitted encodes a genuine semantic
cause, rather than an unrelated token. -/
theorem receiptFor_causal (model : QueryFirstModel) (space : model.Space)
    (revisionTerm : model.Revision → Pattern) (subject result : Pattern)
    (member : result ∈ MeTTaZero.evaluateOne model.zero space subject) :
    ∃ cause : Cause model space subject result,
      receiptFor model space revisionTerm subject result =
        encodeReceipt revisionTerm cause := by
  unfold receiptFor
  rw [dif_pos member]
  exact ⟨(exists_cause_of_mem_evaluateOne model space subject result member).some,
    rfl⟩

def needRequestPattern (spaceTerm subject : Pattern) : Pattern :=
  .apply "prime-need" [spaceTerm, subject]

def needAnswerPattern (answer receipt : Pattern) : Pattern :=
  .apply "prime-need-answer" [answer, receipt]

def reflectedEvaluationPattern (spaceTerm subject : Pattern) : Pattern :=
  .apply "prime-evaluate-name"
    [spaceTerm, .apply "prime-quote" [subject]]

/-- Semantic answer occurrences paired with the finite receipt selected for
their value.  Multiplicity is retained by the multiset, not by distinguishing
equal receipts. -/
noncomputable def semanticNeedEntries (model : QueryFirstModel)
    (space : model.Space)
    (revisionTerm : model.Revision → Pattern) (subject : Pattern) :
    Multiset (Pattern × Pattern) :=
  (MeTTaZero.evaluateOne model.zero space subject).map fun answer =>
    (answer, receiptFor model space revisionTerm subject answer)

/-- The Need answer bag is exactly the Zero answer bag decorated pointwise
with finite causal receipts. -/
noncomputable def semanticNeedAnswers (model : QueryFirstModel)
    (space : model.Space)
    (revisionTerm : model.Revision → Pattern) (subject : Pattern) :
    Multiset Pattern :=
  (semanticNeedEntries model space revisionTerm subject).map fun entry =>
    needAnswerPattern entry.1 entry.2

private theorem needAnswerDecoration_injective (model : QueryFirstModel)
    (space : model.Space) (revisionTerm : model.Revision → Pattern)
    (subject : Pattern) :
    Function.Injective (fun answer =>
      needAnswerPattern answer
        (receiptFor model space revisionTerm subject answer)) := by
  intro first second equal
  simp [needAnswerPattern] at equal
  exact equal.1

/-- Decorating answers with receipts preserves the count of every occurrence. -/
theorem semanticNeedAnswers_count (model : QueryFirstModel)
    (space : model.Space)
    (revisionTerm : model.Revision → Pattern) (subject answer : Pattern) :
    Multiset.count
        (needAnswerPattern answer
          (receiptFor model space revisionTerm subject answer))
        (semanticNeedAnswers model space revisionTerm subject) =
      Multiset.count answer
        (MeTTaZero.evaluateOne model.zero space subject) := by
  rw [semanticNeedAnswers, semanticNeedEntries, Multiset.map_map]
  exact Multiset.count_map_eq_count'
    (fun candidate => needAnswerPattern candidate
      (receiptFor model space revisionTerm subject candidate))
    (MeTTaZero.evaluateOne model.zero space subject)
    (needAnswerDecoration_injective model space revisionTerm subject) answer

/-! ## Current receipt granularity

The current ABI records output occurrences separately but chooses causal
receipts by answer value.  The following executable boundary example makes
that distinction explicit: two equal equation occurrences yield two equal
answer occurrences carrying one and the same value-level receipt.  Therefore
these receipts are sufficient for whole-revision validation, but are not yet
certificates for invalidating only one exact stored occurrence. -/

namespace ReceiptMultiplicityCanary

private def subject : Pattern := .apply "prime-receipt-subject" []

private def result : Pattern := .apply "prime-receipt-result" []

private def equation : Pattern := .apply "=" [subject, result]

private def space : VersionedSpace := (0, {equation, equation})

private def model : QueryFirstModel := structuralModel (fun _ => 0)

private def revisionTerm : Nat → Pattern := fun revision =>
  .apply "revision" [.apply (toString revision) []]

private theorem duplicateEvaluation :
    MeTTaZero.evaluateOne model.zero space subject =
      ({result, result} : Multiset Pattern) := by
  simp [MeTTaZero.evaluateOne, MeTTaZero.interpretedResults,
    MeTTaZero.equationResults, MeTTaZero.queryAll, MeTTaZero.query,
    model, space, structuralModel, matchPattern, matchArgs,
    MeTTaZero.viewEquation?, equation, subject, result, applyBindings]

/-- Two equal result occurrences survive, while their receipt is selected by
the shared result value rather than by an exact source occurrence identity. -/
theorem duplicate_result_occurrences_share_value_receipt :
    Multiset.count
        (needAnswerPattern result
          (receiptFor model space revisionTerm subject result))
        (semanticNeedAnswers model space revisionTerm subject) = 2 := by
  rw [semanticNeedAnswers_count, duplicateEvaluation]
  rfl

/-- One exact occurrence of the duplicated result.  This is the information
retained by Prime's semantic answer carrier and omitted by the value-level
receipt pattern. -/
structure ReceiptOccurrence where
  occurrence : Nat
  copy : occurrence < Multiset.count result
    (MeTTaZero.evaluateOne model.zero space subject)

/-- The current receipt shadow forgets which exact copy it decorates. -/
noncomputable def receiptShadow (_ : ReceiptOccurrence) : Pattern :=
  needAnswerPattern result (receiptFor model space revisionTerm subject result)

def occurrenceNumber (copy : ReceiptOccurrence) : Nat := copy.occurrence

private def firstOccurrence : ReceiptOccurrence where
  occurrence := 0
  copy := by rw [duplicateEvaluation]; decide

private def secondOccurrence : ReceiptOccurrence where
  occurrence := 1
  copy := by rw [duplicateEvaluation]; decide

/-- The two concrete output occurrences form a nontrivial fibre of the current
receipt projection. -/
noncomputable def receiptOccurrenceFiber :
    Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber
      receiptShadow occurrenceNumber where
  left := firstOccurrence
  right := secondOccurrence
  sameShadow := rfl
  differentValue := by decide

/-- Exact result-occurrence identity cannot be reconstructed from the current
value-level receipt.  A successor receipt format needs an occurrence field if
it is to serve as an exact finite-cone authority key. -/
theorem exact_occurrence_does_not_factor_through_value_receipt :
    ¬Mettapedia.GSLT.Core.NonFactorization.Factors
      receiptShadow occurrenceNumber :=
  receiptOccurrenceFiber.not_factors

end ReceiptMultiplicityCanary

private noncomputable def needRows (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject : Pattern) : List (List Pattern) :=
  (semanticNeedEntries model space revisionTerm subject).toList.map
    fun entry => [spaceTerm, subject, entry.1, entry.2]

/-- Prime extends the Zero relation environment with the single `PrimeNeed`
relation.  Query and direct evaluation delegate to the already-proved Zero
environment. -/
noncomputable def relationEnv (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern) :
    RelationEnv where
  tuples relation arguments :=
    match relation, arguments with
    | "PrimeNeed", [candidateSpace, subject, .fvar _, .fvar _] =>
        if candidateSpace = spaceTerm then
          needRows model space spaceTerm revisionTerm subject
        else
          []
    | _, _ =>
        (Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy.relationEnv
          model.zero space spaceTerm).tuples
          relation arguments

@[simp] private theorem match_need_row
    (spaceTerm subject answer receipt : Pattern) :
    matchRelationArgs [("subject", subject), ("space", spaceTerm)]
        [MeTTaZero.metavariable "space", MeTTaZero.metavariable "subject",
          MeTTaZero.metavariable "answer", MeTTaZero.metavariable "receipt"]
        [spaceTerm, subject, answer, receipt] =
      [[("receipt", receipt), ("answer", answer)]] := by
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings, MeTTaZero.metavariable]

@[simp] private theorem match_zero_evaluation_row
    (spaceTerm subject answer : Pattern) :
    matchRelationArgs [("subject", subject), ("space", spaceTerm)]
        [MeTTaZero.metavariable "space", MeTTaZero.metavariable "subject",
          MeTTaZero.metavariable "answer"]
        [spaceTerm, subject, answer] = [[("answer", answer)]] := by
  simp [matchRelationArgs, matchRelationArgument, Bindings.lookup,
    mergeBindings, MeTTaZero.metavariable]

private def needRowResults (spaceTerm subject : Pattern)
    (entries : List (Pattern × Pattern)) : List Pattern :=
  ((entries.map fun entry =>
      [spaceTerm, subject, entry.1, entry.2]).flatMap fun tuple =>
        (matchRelationArgs [("subject", subject), ("space", spaceTerm)]
          [MeTTaZero.metavariable "space", MeTTaZero.metavariable "subject",
            MeTTaZero.metavariable "answer", MeTTaZero.metavariable "receipt"]
          tuple).filterMap fun extension =>
            extension.foldlM
              (init := [("subject", subject), ("space", spaceTerm)])
              fun accumulated entry =>
                match accumulated.find? fun existing =>
                    existing.1 == entry.1 with
                | none => some (entry :: accumulated)
                | some (_, existing) =>
                    if existing = entry.2 then some accumulated else none).map
    fun bindings =>
      needAnswerPattern
        (match bindings.find? fun binding => binding.1 == "answer" with
         | some (_, value) => value
         | none => .fvar "answer")
        (match bindings.find? fun binding => binding.1 == "receipt" with
         | some (_, value) => value
         | none => .fvar "receipt")

@[simp] private theorem execute_need_rows (spaceTerm subject : Pattern)
    (entries : List (Pattern × Pattern)) :
    needRowResults spaceTerm subject entries =
      entries.map fun entry => needAnswerPattern entry.1 entry.2 := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨answer, receipt⟩
      unfold needRowResults at inductionHypothesis ⊢
      simp only [List.map_cons, List.flatMap_cons,
        List.map_append]
      rw [match_need_row, inductionHypothesis]
      simp [needAnswerPattern]

/-! ## Generic execution -/

/-- Prime execution is the ordinary premise-aware interpreter instantiated
with the authored five-field root. -/
noncomputable def executionStep (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (source target : Pattern) : Prop :=
  target ∈ rewriteStepWithPremisesUsing
    (relationEnv model space spaceTerm revisionTerm)
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.language source

/-- The execution relation itself is a GSLT; no Prime-specific machine is
smuggled into the semantic root. -/
noncomputable def executionGSLT (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern) : GSLT where
  Term := Pattern
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := executionStep model space spaceTerm revisionTerm
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Executing an authored Need request produces exactly the semantic Zero
answer bag decorated with causal receipts. -/
theorem need_rewrite_bag_adequate (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject : Pattern) :
    (rewriteStepWithPremisesUsing
        (relationEnv model space spaceTerm revisionTerm)
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.language
        (needRequestPattern spaceTerm subject) : Multiset Pattern) =
      semanticNeedAnswers model space revisionTerm subject := by
  simp (config := { maxSteps := 500000 })
    [rewriteStepWithPremisesUsing, applyRuleWithPremisesUsing,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, relationEnv, needRows,
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.language,
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.evaluationDemandRewrite,
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.needRewrite,
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.needReturnRewrite,
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.reflectedDemandRewrite,
      MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
      MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
      MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
      needRequestPattern,
      MeTTaZero.metavariable, matchPatternForRule,
      matchPatternForRuleUsing, applyBindingsForRule,
      applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
      applyBindings]
  change (needRowResults spaceTerm subject
      (semanticNeedEntries model space revisionTerm subject).toList :
        Multiset Pattern) = _
  rw [execute_need_rows]
  unfold semanticNeedAnswers
  conv_rhs =>
    rw [← Multiset.coe_toList
      (semanticNeedEntries model space revisionTerm subject)]
  rfl

macro "prime_step_simp" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 500000 })
      [executionStep, rewriteStepWithPremisesUsing,
        applyRuleWithPremisesUsing, applyPremisesWithEnv,
        premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.language,
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.evaluationDemandRewrite,
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.needRewrite,
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.needReturnRewrite,
        Mettapedia.Languages.MeTTa.Prime.LanguageDef.reflectedDemandRewrite,
        MeTTaZero.queryRewrite, MeTTaZero.evaluationRewrite,
        MeTTaZero.queryRequestPattern, MeTTaZero.queryAnswerPattern,
        MeTTaZero.evaluationRequestPattern, MeTTaZero.evaluationAnswerPattern,
        needRequestPattern, needAnswerPattern, reflectedEvaluationPattern,
        MeTTaZero.metavariable, matchPatternForRule,
        matchPatternForRuleUsing, applyBindingsForRule,
        applyBindingsForRuleUsing, matchPattern, matchArgs, mergeBindings,
        applyBindings])

/-- The first leg of the semantic lazy route is executable directly from the
authored `evaluationDemandRewrite`. -/
theorem evaluation_demand_exec (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject : Pattern) :
    executionStep model space spaceTerm revisionTerm
      (MeTTaZero.evaluationRequestPattern spaceTerm subject)
      (needRequestPattern spaceTerm subject) := by
  prime_step_simp

/-- The same authored root retains the direct extensional evaluation branch. -/
theorem direct_evaluation_exec (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern)
    (member : result ∈ MeTTaZero.evaluateOne model.zero space subject) :
    executionStep model space spaceTerm revisionTerm
      (MeTTaZero.evaluationRequestPattern spaceTerm subject)
      (MeTTaZero.evaluationAnswerPattern result) := by
  prime_step_simp
  refine ⟨[("answer", result), ("subject", subject), ("space", spaceTerm)], ?_,
    by simp⟩
  refine ⟨[spaceTerm, subject, result], ?_, ?_⟩
  · simpa [relationEnv,
      Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy.relationEnv,
      MeTTaZero.semanticRelationEnv] using member
  · refine ⟨[("answer", result)], ?_, rfl⟩
    rw [show
      matchRelationArgs [("subject", subject), ("space", spaceTerm)]
          [Pattern.fvar "space", Pattern.fvar "subject", Pattern.fvar "answer"]
          [spaceTerm, subject, result] = [[("answer", result)]] by
        simpa [MeTTaZero.metavariable] using
          match_zero_evaluation_row spaceTerm subject result]
    simp

/-- A Need answer returns to the exact Zero observation under the generic
executor, independently of the receipt payload. -/
theorem need_return_exec (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (answer receipt : Pattern) :
    executionStep model space spaceTerm revisionTerm
      (needAnswerPattern answer receipt)
      (MeTTaZero.evaluationAnswerPattern answer) := by
  prime_step_simp

/-- Explicit evaluation of a structural quote enters the same Need request. -/
theorem reflected_demand_exec (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject : Pattern) :
    executionStep model space spaceTerm revisionTerm
      (reflectedEvaluationPattern spaceTerm subject)
      (needRequestPattern spaceTerm subject) := by
  prime_step_simp

/-- Every semantic result gives one generic Need answer step, with the receipt
chosen by `receiptFor`.  Multiplicity is retained by
`need_rewrite_bag_adequate`; this membership theorem selects one copy. -/
theorem need_answer_exec_of_mem (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern)
    (member : result ∈ MeTTaZero.evaluateOne model.zero space subject) :
    executionStep model space spaceTerm revisionTerm
      (needRequestPattern spaceTerm subject)
      (needAnswerPattern result
        (receiptFor model space revisionTerm subject result)) := by
  have outputMember :
      needAnswerPattern result
          (receiptFor model space revisionTerm subject result) ∈
        semanticNeedAnswers model space revisionTerm subject := by
    unfold semanticNeedAnswers semanticNeedEntries
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨result, member, rfl⟩
  unfold executionStep
  change needAnswerPattern result
      (receiptFor model space revisionTerm subject result) ∈
    (rewriteStepWithPremisesUsing
      (relationEnv model space spaceTerm revisionTerm)
      Mettapedia.Languages.MeTTa.Prime.LanguageDef.language
      (needRequestPattern spaceTerm subject) : Multiset Pattern)
  rw [need_rewrite_bag_adequate]
  exact outputMember

/-! ## Route-level correspondence -/

/-- The direct generic route corresponding to one semantic occurrence. -/
noncomputable def authoredDirectPath (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (executionGSLT model space spaceTerm revisionTerm).RewritePath
      (MeTTaZero.evaluationRequestPattern spaceTerm subject)
      (MeTTaZero.evaluationAnswerPattern result) :=
  .cons (direct_evaluation_exec model space spaceTerm revisionTerm
    subject result (Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)))
    (.nil _)

/-- The three authored rewrites execute the same occurrence through Need. -/
noncomputable def authoredLazyPath (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (executionGSLT model space spaceTerm revisionTerm).RewritePath
      (MeTTaZero.evaluationRequestPattern spaceTerm subject)
      (MeTTaZero.evaluationAnswerPattern result) := by
  have member : result ∈ MeTTaZero.evaluateOne model.zero space subject :=
    Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)
  exact .cons (evaluation_demand_exec model space spaceTerm revisionTerm subject)
    (.cons (need_answer_exec_of_mem model space spaceTerm revisionTerm
      subject result member)
      (.cons (need_return_exec model space spaceTerm revisionTerm result
        (receiptFor model space revisionTerm subject result))
        (.nil _)))

/-- Reflective evaluation reaches the same causally decorated Need answer. -/
noncomputable def authoredReflectedPath (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (executionGSLT model space spaceTerm revisionTerm).RewritePath
      (reflectedEvaluationPattern spaceTerm subject)
      (needAnswerPattern result
        (receiptFor model space revisionTerm subject result)) := by
  have member : result ∈ MeTTaZero.evaluateOne model.zero space subject :=
    Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)
  exact .cons (reflected_demand_exec model space spaceTerm revisionTerm subject)
    (.cons (need_answer_exec_of_mem model space spaceTerm revisionTerm
      subject result member) (.nil _))

@[simp] theorem authoredDirectPath_length (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (authoredDirectPath model space spaceTerm revisionTerm subject result
      occurrence copy).length = 1 := rfl

@[simp] theorem authoredLazyPath_length (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (authoredLazyPath model space spaceTerm revisionTerm subject result
      occurrence copy).length = 3 := rfl

@[simp] theorem authoredReflectedPath_length (model : QueryFirstModel)
    (space : model.Space) (spaceTerm : Pattern)
    (revisionTerm : model.Revision → Pattern) (subject result : Pattern)
    (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    (authoredReflectedPath model space spaceTerm revisionTerm subject result
      occurrence copy).length = 2 := rfl

/-- Direct and lazy execution are genuinely distinct paths to one answer. -/
theorem authoredDirectPath_ne_lazyPath (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (MeTTaZero.evaluateOne model.zero space subject)) :
    authoredDirectPath model space spaceTerm revisionTerm subject result
        occurrence copy ≠
      authoredLazyPath model space spaceTerm revisionTerm subject result
        occurrence copy := by
  intro equal
  have lengths := congrArg (fun path => path.length) equal
  simp at lengths

/-! ## Certified realization -/

/-- One proof-relevant semantic occurrence to be realized by the authored
five-field interpreter. -/
structure EvaluationOccurrence (model : QueryFirstModel)
    (space : model.Space) where
  subject : Pattern
  result : Pattern
  occurrence : Nat
  copy : occurrence < Multiset.count result
    (MeTTaZero.evaluateOne model.zero space subject)

/-- The source-side route data already present in Prime's semantic GSLT. -/
def EvaluationOccurrence.semanticComparison {model : QueryFirstModel}
    {space : model.Space} (source : EvaluationOccurrence model space) :
    EvaluationRouteComparison model.toPrimeModel space
      source.subject source.result
      source.occurrence :=
  evaluationRouteComparison model.toPrimeModel space source.subject source.result
    source.occurrence source.copy

/-- A compiled artifact contains actual generic-executor paths and proof that
its emitted receipt came from a semantic cause. -/
structure AuthoredEvaluationArtifact (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern) where
  source : EvaluationOccurrence model space
  direct : (executionGSLT model space spaceTerm revisionTerm).RewritePath
    (MeTTaZero.evaluationRequestPattern spaceTerm source.subject)
    (MeTTaZero.evaluationAnswerPattern source.result)
  lazy : (executionGSLT model space spaceTerm revisionTerm).RewritePath
    (MeTTaZero.evaluationRequestPattern spaceTerm source.subject)
    (MeTTaZero.evaluationAnswerPattern source.result)
  receipt_causal : ∃ cause : Cause model space source.subject source.result,
    receiptFor model space revisionTerm source.subject source.result =
      encodeReceipt revisionTerm cause

/-- The named conservation boundary between semantic and authored routes. -/
structure EvaluationObservation where
  subject : Pattern
  result : Pattern
  occurrence : Nat
  directLength : Nat
  lazyLength : Nat
deriving DecidableEq

noncomputable def compileEvaluation (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (source : EvaluationOccurrence model space) :
    AuthoredEvaluationArtifact model space spaceTerm revisionTerm where
  source := source
  direct := authoredDirectPath model space spaceTerm revisionTerm
    source.subject source.result source.occurrence source.copy
  lazy := authoredLazyPath model space spaceTerm revisionTerm
    source.subject source.result source.occurrence source.copy
  receipt_causal := receiptFor_causal model space revisionTerm
    source.subject source.result
      (Multiset.count_pos.mp (Nat.zero_lt_of_lt source.copy))

def observeSemanticOccurrence {model : QueryFirstModel} {space : model.Space}
    (source : EvaluationOccurrence model space) : EvaluationObservation :=
  { subject := source.subject
    result := source.result
    occurrence := source.occurrence
    directLength := source.semanticComparison.direct.length
    lazyLength := source.semanticComparison.lazy.length }

noncomputable def observeAuthoredArtifact {model : QueryFirstModel}
    {space : model.Space}
    {spaceTerm : Pattern} {revisionTerm : model.Revision → Pattern}
    (artifact : AuthoredEvaluationArtifact model space spaceTerm revisionTerm) :
    EvaluationObservation :=
  { subject := artifact.source.subject
    result := artifact.source.result
    occurrence := artifact.source.occurrence
    directLength := artifact.direct.length
    lazyLength := artifact.lazy.length }

/-- Prime's five-field interpreter is a certified realization of semantic
evaluation occurrences.  The certificate preserves the result occurrence and
the nontrivial direct/lazy route profile; the artifact additionally carries
the executable paths and a causal proof for the result value. -/
noncomputable def evaluationRealization (model : QueryFirstModel)
    (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern) :
    SimpleRealization (EvaluationOccurrence model space)
      (AuthoredEvaluationArtifact model space spaceTerm revisionTerm)
      EvaluationObservation where
  compile := fun _ source =>
    compileEvaluation model space spaceTerm revisionTerm source
  observeSource := fun _ => observeSemanticOccurrence
  observeArtifact := fun _ => observeAuthoredArtifact
  adequate := by
    intro _ source
    cases source with
    | mk subject result occurrence copy =>
        simp [observeSemanticOccurrence, observeAuthoredArtifact,
          EvaluationOccurrence.semanticComparison, compileEvaluation,
          evaluationRouteComparison]

@[simp] theorem evaluationRealization_observation (model : QueryFirstModel)
    (space : model.Space) (spaceTerm : Pattern)
    (revisionTerm : model.Revision → Pattern)
    (source : EvaluationOccurrence model space) :
    (evaluationRealization model space spaceTerm revisionTerm).observeArtifact ()
        ((evaluationRealization model space spaceTerm revisionTerm).compile () source) =
      (evaluationRealization model space spaceTerm revisionTerm).observeSource ()
        source :=
  (evaluationRealization model space spaceTerm revisionTerm).observe_compile ()
    source

/-- The realization cannot collapse to an identity artifact: its compiled
direct and lazy paths are observably different. -/
theorem compiled_paths_distinct (model : QueryFirstModel) (space : model.Space)
    (spaceTerm : Pattern) (revisionTerm : model.Revision → Pattern)
    (source : EvaluationOccurrence model space) :
    (compileEvaluation model space spaceTerm revisionTerm source).direct ≠
      (compileEvaluation model space spaceTerm revisionTerm source).lazy := by
  exact authoredDirectPath_ne_lazyPath model space spaceTerm revisionTerm
    source.subject source.result source.occurrence source.copy

end Mettapedia.Languages.MeTTa.Prime.LanguageDefAdequacy
