import Mettapedia.CognitiveArchitecture.FundedScheduledPremiseService
import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-!
# Value, choice, trace cost, and attention on one premise service

This module places four independent quantitative/control structures on the
concrete foreground-chaining/background-premise-selection workload:

* an optional two-coordinate value for each candidate occurrence;
* an explicit bag-relative maximum resolver;
* a three-coordinate cost valuation of the exact execution trace; and
* the existing independently authorized STI settlement.

The positive run retains all four witnesses.  Negative controls show that a
high-valued choice cannot cross the store-admission boundary, a rejected
candidate still incurs trace cost, and an insufficient engine budget does not
turn the semantic result into a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService

noncomputable section

open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.CognitiveArchitecture.FundedScheduledPremiseService
open Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-! ## Optional vector values and explicit resolution -/

/-- Relevance and support are separate coordinates. -/
abbrev PremiseValue := Fin 2 → Nat

def requiredCandidate : ClauseOccurrence := selectedOccurrenceAt 0

def secondRequiredCandidate : ClauseOccurrence := selectedOccurrenceAt 1

def distractorCandidate : ClauseOccurrence := ⟨77, .distractor⟩

/-- Only bridge and distractor occurrences carry this optional value channel.
Unrelated clauses pay no value-storage cost. -/
def premiseValue : OptionalValuation ClauseOccurrence PremiseValue :=
  fun candidate =>
    match candidate.clause with
    | .bridge => some ![4, 2]
    | .distractor => some ![1, 0]
    | _ => none

def valuePriority (value : PremiseValue) : Nat := value 0 + value 1

def premiseGuidance : Guidance ClauseOccurrence PremiseValue Nat where
  value := premiseValue
  priorityOf := valuePriority
  fallback := fun _candidate => 0

def candidateList : List ClauseOccurrence :=
  [requiredCandidate, distractorCandidate]

def candidateBag : Multiset ClauseOccurrence := candidateList

def selectedServices : Multiset ClauseOccurrence :=
  premiseGuidance.resolveMax candidateBag

@[simp] theorem required_priority :
    premiseGuidance.priority requiredCandidate = 6 :=
  rfl

@[simp] theorem distractor_priority :
    premiseGuidance.priority distractorCandidate = 1 :=
  rfl

@[simp] theorem second_required_priority :
    premiseGuidance.priority secondRequiredCandidate = 6 :=
  rfl

/-- Optional values are conservative annotations of the exact occurrence
sequence. -/
theorem value_attachment_preserves_occurrences :
    (attachOptionalValues premiseValue candidateList).map
        ValuedOccurrence.occurrence = candidateList :=
  erase_attachOptionalValues premiseValue candidateList

/-- The resolver is explicit and bag-relative; on the worked bag it retains
exactly the useful premise occurrence. -/
theorem choice_selects_exact_required :
    selectedServices = {requiredCandidate} := by
  classical
  simp [selectedServices, Guidance.resolveMax, maxSelector, candidateBag,
    candidateList, Guidance.priority, premiseGuidance, premiseValue,
    valuePriority, requiredCandidate, distractorCandidate,
    selectedOccurrenceAt, admittedOccurrence, authorizedSelectionAt,
    selectionReceiptAt, selectorInvocation, Space.occurrenceAt,
    clauseOfPremise]

/-- Equal best values do not collapse distinct occurrence identities. -/
def duplicateCandidateBag : Multiset ClauseOccurrence :=
  {requiredCandidate, secondRequiredCandidate, distractorCandidate}

theorem choice_preserves_equal_best_occurrences :
    requiredCandidate ∈ premiseGuidance.resolveMax duplicateCandidateBag ∧
      secondRequiredCandidate ∈
        premiseGuidance.resolveMax duplicateCandidateBag ∧
      requiredCandidate ≠ secondRequiredCandidate := by
  classical
  have maximal := maxSelector_isMaxSelection premiseGuidance.priority
  constructor
  · apply (maximal duplicateCandidateBag requiredCandidate).2
    constructor
    · simp [duplicateCandidateBag]
    · intro other otherMem
      simp [duplicateCandidateBag] at otherMem
      rcases otherMem with equalRequired | equalSecond | equalDistractor
      · simp_all
      · simp_all
      · simp_all
  constructor
  · apply (maximal duplicateCandidateBag secondRequiredCandidate).2
    constructor
    · simp [duplicateCandidateBag]
    · intro other otherMem
      simp [duplicateCandidateBag] at otherMem
      rcases otherMem with equalRequired | equalSecond | equalDistractor
      · simp_all
      · simp_all
      · simp_all
  · exact repeated_selection_keeps_occurrence_identity.2

/-- Exact maximum remains a whole-bag operation rather than becoming one
candidate-local valued clause. -/
theorem service_choice_is_not_candidate_local :
    ¬ Mettapedia.GSLT.Dynamics.CandidateLocalResolution.CandidateLocalizable
      premiseGuidance.resolveMax :=
  premiseGuidance.resolveMax_not_candidateLocalizable
    (low := distractorCandidate) (high := requiredCandidate) (by decide)

/-! ## Exact trace cost -/

inductive EngineEvent where
  | valueRead (candidate : ClauseOccurrence)
  | resolve (candidates : Multiset ClauseOccurrence)
  | storeAdmission (occurrence : ClauseOccurrence)
  | foregroundTick (occurrence : ClauseOccurrence)
deriving DecidableEq

/-- Steps, matching work, and store writes are independently accounted. -/
abbrev EngineCost := Fin 3 → Nat

def eventCost : EngineEvent → EngineCost
  | .valueRead _candidate => ![1, 1, 0]
  | .resolve candidates => ![1, candidates.card, 0]
  | .storeAdmission _occurrence => ![1, 0, 1]
  | .foregroundTick _occurrence => ![1, 1, 0]

/-- The trace charges both candidate reads, including the losing candidate,
before the resolver, admission, and two real foreground ticks. -/
def executionTrace : List EngineEvent :=
  [.valueRead requiredCandidate,
    .valueRead distractorCandidate,
    .resolve candidateBag,
    .storeAdmission requiredCandidate,
    .foregroundTick requiredCandidate,
    .foregroundTick (goalFrom requiredCandidate)]

def costValuation : Valuation EngineEvent := additive eventCost

def exactSpent : EngineCost := ![6, 6, 1]

theorem executionTrace_cost :
    costValuation.historyGrade executionTrace = some exactSpent := by
  simp [costValuation, executionTrace, Valuation.historyGrade,
    additive, additivePartialMonoid, eventCost, exactSpent,
    candidateBag, candidateList]

/-- An exact additive purse decomposition funds the complete trace. -/
def traceFunding :
    BatchSeparation EngineCost eventCost exactSpent executionTrace where
  frame := 0
  source_eq := by
    funext coordinate
    fin_cases coordinate <;> rfl

/-- The losing candidate consumes score work even though it is absent from the
resolved result bag. -/
theorem rejected_candidate_still_costs :
    eventCost (.valueRead distractorCandidate) = ![1, 1, 0] ∧
      distractorCandidate ∉ selectedServices := by
  constructor
  · rfl
  · rw [choice_selects_exact_required]
    simp [requiredCandidate, distractorCandidate, selectedOccurrenceAt,
      admittedOccurrence, authorizedSelectionAt, selectionReceiptAt,
      selectorInvocation, Space.occurrenceAt, clauseOfPremise]

def insufficientBudget : EngineCost := ![5, 6, 1]

/-- Five step units cannot fund a trace whose exact first coordinate is six. -/
theorem insufficientBudget_refuses_trace :
    ¬ Nonempty
      (BatchSeparation EngineCost eventCost insufficientBudget executionTrace) := by
  rintro ⟨funding⟩
  have firstCoordinate := congrFun funding.source_eq (0 : Fin 3)
  simp [insufficientBudget, batchDemand, executionTrace, eventCost] at firstCoordinate
  omega

/-! ## Value and choice still do not authorize mutation -/

/-- A deliberately misleading value channel assigns the highest priority to
the distractor. -/
def misleadingValue : OptionalValuation ClauseOccurrence PremiseValue :=
  fun candidate =>
    if candidate = distractorCandidate then some ![9, 9]
    else if candidate = requiredCandidate then some ![1, 0]
    else none

def misleadingGuidance : Guidance ClauseOccurrence PremiseValue Nat where
  value := misleadingValue
  priorityOf := valuePriority
  fallback := fun _candidate => 0

def misleadingChoice : Multiset ClauseOccurrence :=
  misleadingGuidance.resolveMax candidateBag

theorem misleading_choice_selects_distractor :
    misleadingChoice = {distractorCandidate} := by
  classical
  simp [misleadingChoice, Guidance.resolveMax, maxSelector, candidateBag,
    candidateList, Guidance.priority, misleadingGuidance, misleadingValue,
    valuePriority, requiredCandidate, distractorCandidate,
    selectedOccurrenceAt, admittedOccurrence, authorizedSelectionAt,
    selectionReceiptAt, selectorInvocation, Space.occurrenceAt,
    clauseOfPremise]

/-- Even a winning value and an explicit resolver cannot manufacture the
authorization needed to cross the real store boundary. -/
theorem high_value_choice_does_not_authorize_store :
    distractorCandidate ∈ misleadingChoice ∧
      ¬ StoreAllows (authorizedSelectionAt 0) distractorCandidate := by
  constructor
  · rw [misleading_choice_selects_distractor]
    simp
  · simp [StoreAllows, distractorCandidate, admittedOccurrence,
      authorizedSelectionAt, selectionReceiptAt, selectorInvocation,
      Space.occurrenceAt, clauseOfPremise]

/-! ## The integrated positive run -/

/-- One record retains the independent choice, trace-funding, scheduling,
settlement, and semantic receipts without converting any into another. -/
structure IntegratedRun where
  exactChoice : selectedServices = {requiredCandidate}
  engineFunding : BatchSeparation EngineCost eventCost exactSpent executionTrace
  serviceRun : FundedScheduledRun
  exactCost : costValuation.historyGrade executionTrace = some exactSpent
  exactGoal : solvedSnapshot.events =
    [⟨goalFrom requiredCandidate, ProofResult.proved⟩]

theorem integrated_run_exists : Nonempty IntegratedRun := by
  obtain ⟨serviceRun⟩ := funded_scheduled_run_exists
  exact ⟨{
    exactChoice := choice_selects_exact_required
    engineFunding := traceFunding
    serviceRun := serviceRun
    exactCost := executionTrace_cost
    exactGoal := rfl }⟩

/-- Budget exhaustion is operational incompleteness, not semantic refutation:
the independent unfunded purse cannot erase the already proved semantic run. -/
theorem unaffordable_is_not_refutation :
    (¬ Nonempty
      (BatchSeparation EngineCost eventCost insufficientBudget executionTrace)) ∧
      solvedSnapshot.events =
        [⟨goalFrom requiredCandidate, ProofResult.proved⟩] :=
  ⟨insufficientBudget_refuses_trace, rfl⟩

/-- Engine cost and STI settlement coexist as distinct exact observations. -/
theorem cost_and_attention_remain_distinct :
    costValuation.historyGrade executionTrace = some exactSpent ∧
      AttentionEconomy.Fund.total premiseSettlement.after =
        AttentionEconomy.Fund.total attentionFund :=
  ⟨executionTrace_cost, settlement_conserves_attention⟩

#print axioms value_attachment_preserves_occurrences
#print axioms choice_selects_exact_required
#print axioms choice_preserves_equal_best_occurrences
#print axioms service_choice_is_not_candidate_local
#print axioms executionTrace_cost
#print axioms rejected_candidate_still_costs
#print axioms insufficientBudget_refuses_trace
#print axioms misleading_choice_selects_distractor
#print axioms high_value_choice_does_not_authorize_store
#print axioms integrated_run_exists
#print axioms unaffordable_is_not_refutation
#print axioms cost_and_attention_remain_distinct

end
end Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
