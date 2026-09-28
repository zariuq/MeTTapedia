import Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding

/-!
# Transport of ordered conditional-premise executions

Changing a step oracle can insert new firing occurrences before old ones.  The
resulting conditional run keeps its contextual assignments and premise order,
while each selected step ordinal is transported by its oracle occurrence
embedding.  Root freshness and relation premises have their own, unchanged
selection list when the language and relation environment are fixed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding

/-- The current root-premise evaluator depends on the relation environment
and bindings, but its language argument does not enter its built-in relation
table. Changing the authored rewrite profile therefore leaves these raw
root results unchanged. -/
theorem premiseStepWithEnv_language_independent
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (bindings : Bindings) (premise : Premise) :
    premiseStepWithEnv relEnv oldLang bindings premise =
      premiseStepWithEnv relEnv newLang bindings premise := by
  cases premise <;> rfl

/-- A successful scoped oracle premise always records a step event at the
premise's authored index. -/
theorem stepResults_event {Evidence : Type} (oracle : StepOracle Evidence)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (assignment completed : Assignment) (event : PremiseEvent Evidence)
    (selected : (event, completed) ∈
      stepResults oracle rule spec ambient index localDepth
        source target assignment) :
    ∃ ordinal evidence, event = .step index ordinal evidence := by
  unfold stepResults at selected
  cases hinst : instantiateAt? rule spec ambient (.premise index 0 0)
      [] localDepth assignment source with
  | none => simp [hinst] at selected
  | some instantiated =>
      by_cases hscope : instantiated.isWellScopedAt
          (localDepth + ambient) = true
      · simp only [hinst, hscope, if_true, List.mem_flatMap] at selected
        obtain ⟨⟨⟨evidence, candidate⟩, ordinal⟩, _, admitted⟩ := selected
        by_cases candidateScope : candidate.isWellScopedAt
            (localDepth + ambient) = true
        · simp only [candidateScope, if_true, List.mem_map] at admitted
          obtain ⟨recovered, _, heq⟩ := admitted
          cases heq
          exact ⟨ordinal, evidence, rfl⟩
        · simp [candidateScope] at admitted
      · simp [hinst, hscope] at selected

/-- A root result is independent of the evidence type carried by step results.
Its selection ordinal and completed assignment are unchanged. -/
theorem rootResults_transport {OldEvidence NewEvidence : Type}
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (spec : RuleBindingSpec)
    (ambient index : Nat) (premise : Premise) (assignment completed : Assignment)
    (oldEvent : PremiseEvent OldEvidence)
    (selected : (oldEvent, completed) ∈
      rootResults relEnv oldLang spec ambient index premise assignment) :
    ∃ ordinal, oldEvent = .root index ordinal ∧
      ((.root index ordinal : PremiseEvent NewEvidence), completed) ∈
        rootResults relEnv newLang spec ambient index premise assignment := by
  by_cases hocc : hasOccurrenceAt spec index = true
  · simp [rootResults, hocc] at selected
  · cases hroot : projectRoot? ambient assignment with
    | none => simp [rootResults, hocc, hroot] at selected
    | some root =>
        simp only [rootResults, hocc, Bool.false_eq_true, if_false,
          hroot, List.mem_filterMap] at selected ⊢
        obtain ⟨⟨raw, ordinal⟩, hresult, hselected⟩ := selected
        rw [premiseStepWithEnv_language_independent relEnv
          oldLang newLang root premise] at hresult
        cases hnext : extendRoot? spec ambient assignment raw with
        | none => simp [hnext] at hselected
        | some next =>
            simp [hnext] at hselected
            cases hselected.2
            exact ⟨ordinal, hselected.1.symm,
              ⟨(raw, ordinal), hresult, by simp [hnext]⟩⟩

/-- A step-event comparison records the instantiated source and the exact
selected position of the old oracle result in the new oracle list. -/
def StepEventTransportAt {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source : Pattern)
    (assignment : Assignment) (oldEvent : PremiseEvent OldEvidence)
    (newEvent : PremiseEvent NewEvidence) : Prop :=
  ∃ instantiated,
    instantiateAt? rule spec ambient (.premise index 0 0) [] localDepth
      assignment source = some instantiated ∧
    ∃ oldOrdinal oldEvidence,
      ∃ (oldBound : oldOrdinal <
        (oldOracle (localDepth + ambient) instantiated).length),
        ∃ newEvidence,
      oldEvent = .step index oldOrdinal oldEvidence ∧
      newEvent = .step index
        ((oracleEmbedding (localDepth + ambient) instantiated).position
          ⟨oldOrdinal, oldBound⟩).val newEvidence ∧
      relatedEvidence oldEvidence newEvidence

/-- Scoped and binder-free step premises use the same exact occurrence
comparison. Root premises retain their original selected root ordinal. -/
def PremiseEventTransportAt {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index : Nat) (premise : Premise) (assignment : Assignment)
    (oldEvent : PremiseEvent OldEvidence)
    (newEvent : PremiseEvent NewEvidence) : Prop :=
  match premise with
  | .scopedStep step =>
      StepEventTransportAt relatedEvidence oldOracle newOracle
        oracleEmbedding rule spec ambient index step.binders.length
        step.source assignment oldEvent newEvent
  | .congruence source _ =>
      StepEventTransportAt relatedEvidence oldOracle newOracle
        oracleEmbedding rule spec ambient index 0 source assignment
        oldEvent newEvent
  | _ =>
      ∃ ordinal, oldEvent = .root index ordinal ∧
        newEvent = .root index ordinal

/-- One selected step result transports with its completed assignment and a
certificate identifying the source and exact new oracle ordinal. -/
theorem stepResults_transport_event {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index localDepth : Nat) (source target : Pattern)
    (assignment completed : Assignment) (oldEvent : PremiseEvent OldEvidence)
    (selected : (oldEvent, completed) ∈
      stepResults oldOracle rule spec ambient index localDepth
        source target assignment) :
    ∃ newEvent,
      (newEvent, completed) ∈
        stepResults newOracle rule spec ambient index localDepth
          source target assignment ∧
      StepEventTransportAt relatedEvidence oldOracle newOracle
        oracleEmbedding rule spec ambient index localDepth source
        assignment oldEvent newEvent := by
  obtain ⟨oldOrdinal, oldEvidence, hevent⟩ :=
    stepResults_event oldOracle rule spec ambient index localDepth
      source target assignment completed oldEvent selected
  subst oldEvent
  obtain ⟨instantiated, hinst, oldBound, newEvidence,
      newSelected, evidenceRelated⟩ :=
    stepResults_transport relatedEvidence oldOracle newOracle
      oracleEmbedding rule spec ambient index localDepth
      source target assignment completed oldOrdinal oldEvidence selected
  refine ⟨.step index
    ((oracleEmbedding (localDepth + ambient) instantiated).position
      ⟨oldOrdinal, oldBound⟩).val newEvidence, newSelected, ?_⟩
  exact ⟨instantiated, hinst, oldOrdinal, oldEvidence,
    oldBound, newEvidence, rfl, rfl, evidenceRelated⟩

/-- Any successful authored premise transports across an oracle embedding.
The root branch retains its ordinal; a step branch carries the exact mapped
ordinal and related evidence in `PremiseEventTransportAt`. -/
theorem premiseResults_transport_event {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index : Nat) (premise : Premise)
    (assignment completed : Assignment) (oldEvent : PremiseEvent OldEvidence)
    (selected : (oldEvent, completed) ∈
      premiseResults oldOracle relEnv oldLang rule spec ambient index
        premise assignment) :
    ∃ newEvent,
      (newEvent, completed) ∈
        premiseResults newOracle relEnv newLang rule spec ambient index
          premise assignment ∧
      PremiseEventTransportAt relatedEvidence oldOracle newOracle
        oracleEmbedding rule spec ambient index premise assignment
        oldEvent newEvent := by
  cases premise with
  | scopedStep step =>
      by_cases hscope : step.isWellScopedAt ambient = true
      · simp only [premiseResults, hscope, if_true] at selected ⊢
        exact stepResults_transport_event relatedEvidence oldOracle
          newOracle oracleEmbedding rule spec ambient index
          step.binders.length step.source step.target assignment completed
          oldEvent selected
      · simp [premiseResults, hscope] at selected
  | congruence source target =>
      exact stepResults_transport_event relatedEvidence oldOracle
        newOracle oracleEmbedding rule spec ambient index 0 source target
        assignment completed oldEvent selected
  | freshness fc =>
      obtain ⟨ordinal, hevent, selected'⟩ :=
        rootResults_transport (OldEvidence := OldEvidence)
          (NewEvidence := NewEvidence) relEnv oldLang newLang spec ambient index
          (.freshness fc) assignment completed oldEvent selected
      exact ⟨.root index ordinal, selected', ⟨ordinal, hevent, rfl⟩⟩
  | relationQuery name arguments =>
      obtain ⟨ordinal, hevent, selected'⟩ :=
        rootResults_transport (OldEvidence := OldEvidence)
          (NewEvidence := NewEvidence) relEnv oldLang newLang spec ambient index
          (.relationQuery name arguments) assignment completed oldEvent selected
      exact ⟨.root index ordinal, selected', ⟨ordinal, hevent, rfl⟩⟩
  | forAll collection param body =>
      obtain ⟨ordinal, hevent, selected'⟩ :=
        rootResults_transport (OldEvidence := OldEvidence)
          (NewEvidence := NewEvidence) relEnv oldLang newLang spec ambient index
          (.forAll collection param body) assignment completed oldEvent selected
      exact ⟨.root index ordinal, selected', ⟨ordinal, hevent, rfl⟩⟩

/-- An ordered comparison records a contextual assignment at each premise
boundary. Consequently every step position is interpreted at the source
actually produced by its preceding premise assignments. -/
inductive RunTransport {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    Nat → List Premise → Assignment → Assignment →
      List (PremiseEvent OldEvidence) →
      List (PremiseEvent NewEvidence) → Prop where
  | nil (index : Nat) (assignment : Assignment) :
      RunTransport relatedEvidence oldOracle newOracle oracleEmbedding
        relEnv oldLang newLang rule spec ambient index [] assignment assignment [] []
  | cons {index : Nat} {premise : Premise} {rest : List Premise}
      {initial completed final : Assignment}
      {oldEvent : PremiseEvent OldEvidence}
      {newEvent : PremiseEvent NewEvidence}
      {oldHistory : List (PremiseEvent OldEvidence)}
      {newHistory : List (PremiseEvent NewEvidence)}
      (oldSelected : (oldEvent, completed) ∈
        premiseResults oldOracle relEnv oldLang rule spec ambient index
          premise initial)
      (newSelected : (newEvent, completed) ∈
        premiseResults newOracle relEnv newLang rule spec ambient index
          premise initial)
      (head : PremiseEventTransportAt relatedEvidence oldOracle newOracle
        oracleEmbedding rule spec ambient index premise initial
        oldEvent newEvent)
      (tail : RunTransport relatedEvidence oldOracle newOracle
        oracleEmbedding relEnv oldLang newLang rule spec ambient (index + 1) rest
        completed final oldHistory newHistory) :
      RunTransport relatedEvidence oldOracle newOracle oracleEmbedding
        relEnv oldLang newLang rule spec ambient index (premise :: rest) initial final
        (oldEvent :: oldHistory) (newEvent :: newHistory)

/-- Any old ordered premise run has a new run with the same final contextual
assignment. The comparison records every root ordinal unchanged and every
scoped step ordinal at its exact embedded occurrence, in authored order. -/
theorem runPremises_transport {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    ∀ (index : Nat) (premises : List Premise)
      (initial final : Assignment)
      (oldHistory : List (PremiseEvent OldEvidence)),
      (final, oldHistory) ∈
        runPremises oldOracle relEnv oldLang rule spec ambient
          index premises initial →
      ∃ newHistory,
        (final, newHistory) ∈
          runPremises newOracle relEnv newLang rule spec ambient
            index premises initial ∧
        RunTransport relatedEvidence oldOracle newOracle
          oracleEmbedding relEnv oldLang newLang rule spec ambient index premises
          initial final oldHistory newHistory := by
  intro index premises
  induction premises generalizing index with
  | nil =>
      intro initial final oldHistory selected
      simp only [runPremises, List.mem_singleton, Prod.mk.injEq] at selected
      obtain ⟨hfinal, hhistory⟩ := selected
      subst final
      subst oldHistory
      exact ⟨[], by simp [runPremises], RunTransport.nil index initial⟩
  | cons premise rest inductionHypothesis =>
      intro initial final oldHistory selected
      simp only [runPremises, List.mem_flatMap, List.mem_map] at selected
      obtain ⟨⟨oldEvent, completed⟩, oldSelected,
        ⟨nextFinal, oldTail⟩, tailSelected, hresult⟩ := selected
      cases hresult
      obtain ⟨newEvent, newSelected, headRelated⟩ :=
        premiseResults_transport_event relatedEvidence oldOracle
          newOracle oracleEmbedding relEnv oldLang newLang rule spec ambient index
          premise initial completed oldEvent oldSelected
      obtain ⟨newTail, newTailSelected, tailRelated⟩ :=
        inductionHypothesis (index + 1) completed nextFinal oldTail
          tailSelected
      refine ⟨newEvent :: newTail, ?_,
        RunTransport.cons oldSelected newSelected headRelated tailRelated⟩
      simp only [runPremises, List.mem_flatMap, List.mem_map]
      exact ⟨(newEvent, completed), newSelected,
      (nextFinal, newTail), newTailSelected, rfl⟩

/-- The final scope check and reduct construction depend on the completed
assignment, not on the evidence type or premise ordinals in the history. -/
theorem finish?_transport {OldEvidence NewEvidence : Type}
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (captured completed : Assignment)
    (oldHistory : List (PremiseEvent OldEvidence))
    (newHistory : List (PremiseEvent NewEvidence))
    (oldFiring : RuleFiring OldEvidence)
    (selected : finish? rule spec ambient captured completed oldHistory =
      some oldFiring) :
    oldFiring =
      RuleFiring.mk captured completed oldHistory oldFiring.target ∧
    finish? rule spec ambient captured completed newHistory =
      some (RuleFiring.mk captured completed newHistory oldFiring.target) := by
  unfold finish? at selected ⊢
  cases hred : reduct? rule spec ambient completed with
  | none => simp [hred] at selected
  | some target =>
      by_cases hscope : target.isWellScopedAt ambient = true
      · simp [hred, hscope] at selected ⊢
        cases selected
        exact ⟨rfl, rfl⟩
      · simp [hred, hscope] at selected

/-- A whole authored firing transports through its ordered premise run.
Its capture, completed assignment, and reduct stay fixed; the new history
retains the per-premise exact occurrence comparisons. -/
theorem applyRuleWithOracle_transport {OldEvidence NewEvidence : Type}
    (relatedEvidence : OldEvidence → NewEvidence → Prop)
    (oldOracle : StepOracle OldEvidence)
    (newOracle : StepOracle NewEvidence)
    (oracleEmbedding : ∀ depth source,
      Embedding
        (fun oldValue newValue =>
          oldValue.2 = newValue.2 ∧
            relatedEvidence oldValue.1 newValue.1)
        (oldOracle depth source) (newOracle depth source))
    (relEnv : RelationEnv) (oldLang newLang : LanguageDef)
    (ambient : Nat) (rule : RewriteRule) (term : Pattern)
    (oldFiring : RuleFiring OldEvidence)
    (selected : oldFiring ∈
      applyRuleWithOracle oldOracle relEnv oldLang ambient rule term) :
    ∃ spec newFiring,
      rule.bindings = some spec ∧
      newFiring ∈
        applyRuleWithOracle newOracle relEnv newLang ambient rule term ∧
      newFiring.captured = oldFiring.captured ∧
      newFiring.completed = oldFiring.completed ∧
      newFiring.target = oldFiring.target ∧
      RunTransport relatedEvidence oldOracle newOracle oracleEmbedding
        relEnv oldLang newLang rule spec ambient 0 rule.premises oldFiring.captured
        oldFiring.completed oldFiring.history newFiring.history := by
  obtain ⟨spec, captured, completed, oldHistory, hspec, hadmitted,
      hcaptured, oldRun, oldFinish⟩ :=
    (mem_applyRuleWithOracle_iff oldOracle relEnv oldLang ambient rule
      term oldFiring).mp selected
  obtain ⟨newHistory, newRun, historyRelated⟩ :=
    runPremises_transport relatedEvidence oldOracle newOracle
      oracleEmbedding relEnv oldLang newLang rule spec ambient 0 rule.premises
      captured completed oldHistory oldRun
  obtain ⟨oldShape, newFinish⟩ :=
    finish?_transport rule spec ambient captured completed
      oldHistory newHistory oldFiring oldFinish
  have hcaptureEq : oldFiring.captured = captured :=
    congrArg RuleFiring.captured oldShape
  have hcompleted : oldFiring.completed = completed :=
    congrArg RuleFiring.completed oldShape
  have hhistory : oldFiring.history = oldHistory :=
    congrArg RuleFiring.history oldShape
  let newFiring : RuleFiring NewEvidence :=
    { captured := captured, completed := completed,
      history := newHistory, target := oldFiring.target }
  have newSelected : newFiring ∈
      applyRuleWithOracle newOracle relEnv newLang ambient rule term :=
    (mem_applyRuleWithOracle_iff newOracle relEnv newLang ambient rule
      term newFiring).mpr
        ⟨spec, captured, completed, newHistory, hspec, hadmitted,
          hcaptured, newRun, newFinish⟩
  refine ⟨spec, newFiring, hspec, newSelected, ?_, ?_, ?_, ?_⟩
  · exact hcaptureEq.symm
  · exact hcompleted.symm
  · rfl
  · simpa only [newFiring, hcaptureEq, hcompleted, hhistory] using
      historyRelated

#print axioms premiseStepWithEnv_language_independent
#print axioms stepResults_event
#print axioms rootResults_transport
#print axioms stepResults_transport_event
#print axioms premiseResults_transport_event
#print axioms runPremises_transport
#print axioms finish?_transport
#print axioms applyRuleWithOracle_transport

end Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
