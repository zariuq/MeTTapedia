import Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
import Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService

/-!
# A real valued and costed premise service in the recurrent portfolio

The five-role recurrent controller contains a premise-selection slot once per
cycle.  This module binds that slot to the existing executable Chapter-13
premise selector and retains, as separate evidence:

* the checked source transition and generated portfolio occurrence;
* the scheduler epoch and the domain-service request epoch;
* the exact algorithmic selection receipt and store authorization;
* optional vector value plus explicit bag-relative choice;
* exact three-coordinate trace cost and its per-invocation funding; and
* ECAN long-term protection.

Scheduler time is not identified with service-request time.  The first
premise-selection slot occurs at scheduler epoch three but serves request epoch
zero.  An explicit binding retains both clocks.  This is important for a real
OS-thread realization, where queue position, trigger time, logical request ID,
and completion time need not coincide.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.CognitiveArchitecture.FundedScheduledPremiseService
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.CognitiveArchitecture.ValuedCostedPremiseService
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.Dynamics.TypedValueGeometry
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## The authored two-clock binding -/

/-- Premise selection is the fourth controller action in each five-action
cycle, counting from zero. -/
def schedulerEpoch (cycle : Nat) : Nat := 5 * cycle + 3

/-- Five applications of the role transition return to the same role. -/
theorem nextRole_five : nextRole^[5] = id := by
  funext role
  cases role <;> rfl

/-- At the premise-selection scheduler epoch, PLN is the source role. -/
theorem portfolio_state_before_premise (cycle : Nat) :
    portfolioExecution.state (schedulerEpoch cycle) = .pln := by
  change (nextRole^[5 * cycle + 3]) .foregroundChaining = .pln
  rw [Function.iterate_add_apply, Function.iterate_mul, nextRole_five,
    Function.iterate_id]
  rfl

def portfolioLocalValidity :
    portfolioClaim.controller.LocallyValid
      (auditedLabeledSystem portfolioStepAuthority foregroundAccepting)
      portfolioClaim.root :=
  ((ProgressMeasure.check_eq_true_iff
    (auditedLabeledSystem portfolioStepAuthority foregroundAccepting)
    portfolioController portfolioMeasure portfolioClaim.root).mp
      portfolio_checker_accepts).1

/-- The exact checked source occurrence allocated to premise selection in one
controller cycle. -/
def sourceOccurrence (cycle : Nat) :
    ControlledOccurrence portfolioTheory portfolioStepAuthority.Certificate :=
  occurrenceAt portfolioStepAuthority portfolioClaim portfolioExecution
    (schedulerEpoch cycle)

/-- Its authored triggered-space realization. -/
def portfolioPremiseOccurrence (cycle : Nat) : Occurrence :=
  portfolioCodec.realize (sourceOccurrence cycle)

@[simp] theorem portfolioPremiseOccurrence_schedulerEpoch (cycle : Nat) :
    (portfolioPremiseOccurrence cycle).generatedAt = schedulerEpoch cycle :=
  rfl

/-- The controller slot is bound to the exact premise-selection resident. -/
@[simp] theorem portfolioPremiseOccurrence_role (cycle : Nat) :
    (portfolioPremiseOccurrence cycle).resident = .premiseSelection := by
  change nextRole (portfolioExecution.state (schedulerEpoch cycle)) =
    .premiseSelection
  rw [portfolio_state_before_premise]
  rfl

/-- The logical service epoch counts requests, independently from scheduler
ticks. -/
def serviceInvocation (cycle : Nat) :
    TriggeredOccurrence Unit ResidentService :=
  selectorInvocation cycle

@[simp] theorem serviceInvocation_epoch (cycle : Nat) :
    (serviceInvocation cycle).generatedAt = cycle :=
  rfl

/-- The two clocks are intentionally not identified even on the first cycle. -/
theorem first_scheduler_and_service_epochs_are_distinct :
    (portfolioPremiseOccurrence 0).generatedAt = 3 /\
      (serviceInvocation 0).generatedAt = 0 /\
      (portfolioPremiseOccurrence 0).generatedAt ≠
        (serviceInvocation 0).generatedAt := by
  decide

/-! ## Per-request value, choice, and trace cost -/

def candidateListAt (cycle : Nat) : List ClauseOccurrence :=
  [selectedOccurrenceAt cycle, distractorCandidate]

def candidateBagAt (cycle : Nat) : Multiset ClauseOccurrence :=
  candidateListAt cycle

def selectedServicesAt (cycle : Nat) : Multiset ClauseOccurrence :=
  premiseGuidance.resolveMax (candidateBagAt cycle)

/-- Every request selects its own fresh bridge occurrence rather than the
structurally equal occurrence of an earlier request. -/
theorem choice_selects_exact_request_occurrence (cycle : Nat) :
    selectedServicesAt cycle = {selectedOccurrenceAt cycle} := by
  classical
  simp [selectedServicesAt, Guidance.resolveMax, maxSelector, candidateBagAt,
    candidateListAt, premiseGuidance, premiseValue, valuePriority,
    distractorCandidate, selectedOccurrenceAt, admittedOccurrence,
    authorizedSelectionAt, selectionReceiptAt, selectorInvocation,
    Space.occurrenceAt, clauseOfPremise]

/-- The complete engine trace for one request.  It charges the losing value
read and resolver work before admission and foreground activation. -/
def executionTraceAt (cycle : Nat) : List EngineEvent :=
  [.valueRead (selectedOccurrenceAt cycle),
    .valueRead distractorCandidate,
    .resolve (candidateBagAt cycle),
    .storeAdmission (selectedOccurrenceAt cycle),
    .foregroundTick (selectedOccurrenceAt cycle),
    .foregroundTick (goalFrom (selectedOccurrenceAt cycle))]

theorem executionTraceAt_cost (cycle : Nat) :
    costValuation.historyGrade (executionTraceAt cycle) = some exactSpent := by
  simp [costValuation, executionTraceAt, Valuation.historyGrade,
    additive, additivePartialMonoid, eventCost, exactSpent,
    candidateBagAt, candidateListAt]

/-- Each potential invocation has an exact independent purse.  This is not a
claim that one finite purse funds the infinite recurrent service. -/
def traceFundingAt (cycle : Nat) :
    BatchSeparation EngineCost eventCost exactSpent (executionTraceAt cycle) where
  frame := 0
  source_eq := by
    funext coordinate
    fin_cases coordinate <;> rfl

/-! ## One proof-relevant recurring service receipt -/

/-- All authorities associated with one recurrent premise-service opportunity.
No field is derivable merely from the value or cost fields. -/
structure RecurringPremiseReceipt (cycle : Nat) where
  sourceChecked :
    (auditedRevisionTheory portfolioStepAuthority foregroundAccepting).Step
      (sourceOccurrence cycle).action
      (sourceOccurrence cycle).source
      (sourceOccurrence cycle).target
  portfolioGenerated :
    serviceSpace.Generated heartbeatTrace (schedulerEpoch cycle)
      (portfolioPremiseOccurrence cycle)
  portfolioSelected :
    selectedGenerated (schedulerEpoch cycle)
      (portfolioPremiseOccurrence cycle)
  roleBound : (portfolioPremiseOccurrence cycle).resident = .premiseSelection
  domainInvocationGenerated :
    selectorSpace.Generated heartbeat cycle (serviceInvocation cycle)
  clockBinding :
    (selectionReceiptAt cycle).recommendation.invocation =
      serviceInvocation cycle
  algorithmSelected :
    (selectionReceiptAt cycle).recommendation.selected ∈ selectedPremises
  storeAuthorized :
    StoreAllows (authorizedSelectionAt cycle) (selectedOccurrenceAt cycle)
  exactChoice : selectedServicesAt cycle = {selectedOccurrenceAt cycle}
  exactCost :
    costValuation.historyGrade (executionTraceAt cycle) = some exactSpent
  engineFunding :
    BatchSeparation EngineCost eventCost exactSpent (executionTraceAt cycle)
  longTermProtected : portfolioEconomy.LongTermProtected 1 .premiseSelection

def recurringPremiseReceipt (cycle : Nat) : RecurringPremiseReceipt cycle where
  sourceChecked := audited_step_at portfolioStepAuthority foregroundAccepting
    portfolioClaim portfolioLocalValidity portfolioExecution
    (schedulerEpoch cycle)
  portfolioGenerated := by
    have generated :=
      portfolioCodec.realize_generated (sourceOccurrence cycle)
    change serviceSpace.Generated heartbeatTrace
      (portfolioPremiseOccurrence cycle).generatedAt
      (portfolioPremiseOccurrence cycle) at generated
    rw [portfolioPremiseOccurrence_schedulerEpoch] at generated
    exact generated
  portfolioSelected := by
    have generated :=
      portfolioCodec.realize_generated (sourceOccurrence cycle)
    change serviceSpace.Generated heartbeatTrace
      (portfolioPremiseOccurrence cycle).generatedAt
      (portfolioPremiseOccurrence cycle) at generated
    rw [portfolioPremiseOccurrence_schedulerEpoch] at generated
    exact generated
  roleBound := portfolioPremiseOccurrence_role cycle
  domainInvocationGenerated := selectorInvocation_generated cycle
  clockBinding := rfl
  algorithmSelected := (selectionReceiptAt cycle).selectedByAlgorithm
  storeAuthorized := rfl
  exactChoice := choice_selects_exact_request_occurrence cycle
  exactCost := executionTraceAt_cost cycle
  engineFunding := traceFundingAt cycle
  longTermProtected := every_role_longTermProtected .premiseSelection

/-- Concrete service opportunities with complete typed receipts occur beyond
every finite scheduler bound. -/
theorem premise_service_receipts_recur :
    forall lowerBound, exists cycle,
      lowerBound ≤ schedulerEpoch cycle /\
        Nonempty (RecurringPremiseReceipt cycle) := by
  intro lowerBound
  refine ⟨lowerBound, ?_, ⟨recurringPremiseReceipt lowerBound⟩⟩
  simp [schedulerEpoch]
  omega

/-- Repeated requests may select structurally equal bridge clauses while
retaining distinct domain occurrence identity. -/
theorem repeated_requests_keep_occurrence_identity
    {first second : Nat} (different : first ≠ second) :
    (selectedOccurrenceAt first).clause =
        (selectedOccurrenceAt second).clause /\
      selectedOccurrenceAt first ≠ selectedOccurrenceAt second := by
  constructor
  · rfl
  · intro equalOccurrences
    have equalIds := congrArg ClauseOccurrence.occurrenceId equalOccurrences
    simp [selectedOccurrenceAt, admittedOccurrence, authorizedSelectionAt,
      selectionReceiptAt, selectorInvocation, Space.occurrenceAt] at equalIds
    omega

/-! ## Connection to the actual foreground result and negative controls -/

/-- Request epoch zero is the existing fully executed foreground/background
run.  Its recurring portfolio opportunity coexists with the real goal and the
integrated V/choice/cost/attention receipt. -/
theorem first_recurring_service_has_real_foreground_result :
    Nonempty (RecurringPremiseReceipt 0) /\
      solvedSnapshot.events =
        [⟨goalFrom (selectedOccurrenceAt 0), ProofResult.proved⟩] /\
      Nonempty IntegratedRun :=
  ⟨⟨recurringPremiseReceipt 0⟩,
    background_premise_service_unblocks_foreground.2.2.2.1,
    integrated_run_exists⟩

/-- A recurring generated, selected, valued, and funded control receipt cannot
prove an unrelated semantically impossible service. -/
theorem recurring_control_does_not_prove_arbitrary_service :
    Nonempty (RecurringPremiseReceipt 0) /\
      IsEmpty unavailableRequest.Fulfillment :=
  ⟨⟨recurringPremiseReceipt 0⟩, unavailableRequest_has_no_fulfillment⟩

/-- Value resolution remains advisory at every recurrence: the existing
high-valued distractor for the first request still lacks store authority. -/
theorem recurring_value_does_not_mint_store_authority :
    Nonempty (RecurringPremiseReceipt 0) /\
      distractorCandidate ∈ misleadingChoice /\
      ¬ StoreAllows (authorizedSelectionAt 0) distractorCandidate :=
  ⟨⟨recurringPremiseReceipt 0⟩, high_value_choice_does_not_authorize_store⟩

#print axioms nextRole_five
#print axioms portfolio_state_before_premise
#print axioms first_scheduler_and_service_epochs_are_distinct
#print axioms choice_selects_exact_request_occurrence
#print axioms executionTraceAt_cost
#print axioms premise_service_receipts_recur
#print axioms repeated_requests_keep_occurrence_identity
#print axioms first_recurring_service_has_real_foreground_result
#print axioms recurring_control_does_not_prove_arbitrary_service
#print axioms recurring_value_does_not_mint_store_authority

end
end Mettapedia.CognitiveArchitecture.RecurringValuedCostedPremiseService
