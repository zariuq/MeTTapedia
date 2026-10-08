import Mettapedia.Logic.HMLResidualEvidence
import Mettapedia.OSLF.Framework.FundedNuAssays

/-!
# Received-state assays with actual paid modal instruction prefixes

A receipt retains one actual request/offer delivery and an actual instruction
prefix inspecting the delivered state. Session, provider, client and received
value are retained. The public packet is read only from a completed instruction
configuration; unfinished paid work has no verdict.

The existing aggregate assay price equals the independently compiled
instruction count. A reporting instruction prefix earns its complete price
and the original modal certificate. Its ledger includes the real delivery
charge and every successfully executed instruction. This account does not
identify machine instructions with physical time or compiler implementation
work, nor authenticate externally supplied offers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuInstructionAssays

open Mettapedia.Logic.ModalMuCalculus
open Inspection Unfolding
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Core.InteractionEvent
open FundedNuAssays

open StackInspection

universe u v w z

variable {State : Type u} {Action : Type v} {Providers : Type w} {Clients : Type z}
variable [DecidableEq State] [DecidableEq Providers] [DecidableEq Clients]

structure Receipt (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    (request : Request (Question Action) State Providers Clients) (budget : Nat) where
  received : State
  offered : request.arrival = some received
  delivery : Occurrence
    (AssayProbeDelivery.paid ((protocol presentation deliveryCost).test request.question)
      (deliveryCost request.question) ((protocol presentation deliveryCost).inspectionCost request.question)).presentation
    (AssayProbeDelivery.paidOffered request.session request.provider request.client received budget)
    (AssayProbeDelivery.paidReceived request.session request.provider request.client received
      (budget - deliveryCost request.question received))
  inspection : Funded.Prefix presentation (request.question.1.atStage request.question.2)
    (request.question.1.stage_admitted request.question.2) emptyEnvironment received []
    (budget - deliveryCost request.question received)

variable (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    {request : Request (Question Action) State Providers Clients} {budget : Nat}

namespace Receipt

def responses (receipt : Receipt presentation deliveryCost request budget) : Multiset (Response State Clients) :=
  match Funded.publicAnswer receipt.inspection.endpoint with
  | none => 0
  | some answer => {(request.session, verdictOf answer, request.client, receipt.received)}

def spent (receipt : Receipt presentation deliveryCost request budget) : Nat :=
  deliveryCost request.question receipt.received + receipt.inspection.endpoint.spent

def remaining (receipt : Receipt presentation deliveryCost request budget) : Nat :=
  receipt.inspection.endpoint.remaining

theorem delivery_affordable (receipt : Receipt presentation deliveryCost request budget) :
    deliveryCost request.question receipt.received ≤ budget :=
  ((AssayProbeDelivery.paid_offered_step_iff
    ((protocol presentation deliveryCost).test request.question) (deliveryCost request.question)
    ((protocol presentation deliveryCost).inspectionCost request.question)
    request.session request.provider request.client receipt.received budget _).1 receipt.delivery.step).1

theorem ledger (receipt : Receipt presentation deliveryCost request budget) :
    budget = receipt.remaining + receipt.spent := by
  have delivery := receipt.delivery_affordable presentation deliveryCost
  have inspection := receipt.inspection.ledger presentation _ _ emptyEnvironment receipt.received [] _
  dsimp only [remaining, spent]
  omega

theorem unfinished_is_quiet (receipt : Receipt presentation deliveryCost request budget)
    (unfinished : receipt.inspection.endpoint.pending ≠ []) : receipt.responses = 0 := by
  simp only [responses, Funded.publicAnswer_unfinished _ unfinished]

theorem response_readout (receipt : Receipt presentation deliveryCost request budget)
    (response : Response State Clients) (present : response ∈ receipt.responses) :
    ∃ answer : Bool, Funded.publicAnswer receipt.inspection.endpoint = some answer ∧
      response = (request.session, verdictOf answer, request.client, receipt.received) := by
  cases reported : Funded.publicAnswer receipt.inspection.endpoint with
  | none => simp only [responses, reported, Multiset.notMem_zero] at present
  | some answer =>
      exact ⟨answer, rfl, by
        simpa only [responses, reported, Multiset.mem_singleton] using present⟩

theorem reporting_certificate (receipt : Receipt presentation deliveryCost request budget)
    (answer : Bool) (reported : Funded.publicAnswer receipt.inspection.endpoint = some answer) :
    StageCertificate presentation request.question (verdictOf answer) receipt.received := by
  have certified := (receipt.inspection.answer_sound presentation _ _ emptyEnvironment receipt.received [] _
    answer reported).2.2
  cases answer <;>
    simpa only [Funded.ModalCertificate, StageCertificate, verdictOf, emptyEnvironment_read] using certified

theorem reporting_spent (receipt : Receipt presentation deliveryCost request budget)
    (answer : Bool) (reported : Funded.publicAnswer receipt.inspection.endpoint = some answer) :
    receipt.spent = deliveryCost request.question receipt.received +
      (protocol presentation deliveryCost).inspectionCost request.question receipt.received := by
  unfold spent
  rw [receipt.inspection.reporting_spent presentation _ _ emptyEnvironment receipt.received [] _ answer reported]
  rfl

theorem response_certificate (receipt : Receipt presentation deliveryCost request budget)
    (response : Response State Clients) (present : response ∈ receipt.responses) :
    ∃ answer : Bool, request.arrival = some receipt.received ∧
      response = (request.session, verdictOf answer, request.client, receipt.received) ∧
      StageCertificate presentation request.question (verdictOf answer) receipt.received ∧
      receipt.spent = deliveryCost request.question receipt.received +
        (protocol presentation deliveryCost).inspectionCost request.question receipt.received ∧
      receipt.spent ≤ budget := by
  obtain ⟨answer, reported, readout⟩ := receipt.response_readout presentation deliveryCost response present
  have conserved := receipt.ledger presentation deliveryCost
  exact ⟨answer, receipt.offered, readout,
    receipt.reporting_certificate presentation deliveryCost answer reported,
    receipt.reporting_spent presentation deliveryCost answer reported, by omega⟩

/-- Failure of a completed unfolding test refutes the original greatest
fixed point, without assuming a finite state carrier. -/
theorem received_refutation (receipt : Receipt presentation deliveryCost request budget)
    (reported : Funded.publicAnswer receipt.inspection.endpoint = some false) :
    ¬ satisfies presentation.toLTS Env.empty (.nu request.question.1.body) receipt.received :=
  refuted_stage_refutes_original presentation.toLTS request.question.1 request.question.2 receipt.received
    (receipt.reporting_certificate presentation deliveryCost false reported)

theorem received_finite_confirmation [Finite State]
    (receipt : Receipt presentation deliveryCost request budget)
    (enough : Nat.card State ≤ request.question.2)
    (reported : Funded.publicAnswer receipt.inspection.endpoint = some true) :
    satisfies presentation.toLTS Env.empty (.nu request.question.1.body) receipt.received :=
  (finite_stage_equals_original presentation.toLTS request.question.1 request.question.2 enough
    receipt.received).1 (receipt.reporting_certificate presentation deliveryCost true reported)

end Receipt

def inspectReceived (request : Request (Question Action) State Providers Clients)
    (budget : Nat) (state : State) (offered : request.arrival = some state)
    (deliveryAffordable : deliveryCost request.question state ≤ budget) :
    Receipt presentation deliveryCost request budget where
  received := state
  offered := offered
  delivery := ⟨.inr ⟨()⟩, ⟨AssayProbeDelivery.deliver request.session request.provider request.client state,
    (AssayProbeDelivery.delivery_enabled_iff ((protocol presentation deliveryCost).test request.question)
      (deliveryCost request.question) ((protocol presentation deliveryCost).inspectionCost request.question)
      request.session request.provider request.client state budget).2 deliveryAffordable,
    (AssayProbeDelivery.delivery_fire_paid ((protocol presentation deliveryCost).test request.question)
      (deliveryCost request.question) ((protocol presentation deliveryCost).inspectionCost request.question)
      request.session request.provider request.client state budget).symm⟩⟩
  inspection := Funded.attempt presentation (request.question.1.atStage request.question.2)
    (request.question.1.stage_admitted request.question.2) emptyEnvironment state []
      (budget - deliveryCost request.question state)

theorem inspectReceived_responses (request : Request (Question Action) State Providers Clients)
    (budget : Nat) (state : State) (offered : request.arrival = some state)
    (deliveryAffordable : deliveryCost request.question state ≤ budget) :
    (inspectReceived presentation deliveryCost request budget state offered deliveryAffordable).responses =
      if deliveryCost request.question state +
        (protocol presentation deliveryCost).inspectionCost request.question state ≤ budget then
          {(request.session, verdictOf ((protocol presentation deliveryCost).test request.question state),
            request.client, state)} else 0 := by
  unfold Receipt.responses inspectReceived
  rw [Funded.attempt_answer]
  change (match (if (protocol presentation deliveryCost).inspectionCost request.question state ≤
      budget - deliveryCost request.question state then
        some ((protocol presentation deliveryCost).test request.question state) else none) with
    | none => (0 : Multiset (Response State Clients))
    | some answer => {(request.session, verdictOf answer, request.client, state)}) =
      (if deliveryCost request.question state +
        (protocol presentation deliveryCost).inspectionCost request.question state ≤ budget then
          {(request.session, verdictOf ((protocol presentation deliveryCost).test request.question state),
            request.client, state)} else (0 : Multiset (Response State Clients)))
  by_cases affordable : deliveryCost request.question state +
      (protocol presentation deliveryCost).inspectionCost request.question state ≤ budget
  · have inspection : (protocol presentation deliveryCost).inspectionCost request.question state ≤
        budget - deliveryCost request.question state := by omega
    simp only [if_pos affordable, if_pos inspection]
  · have inspection : ¬ (protocol presentation deliveryCost).inspectionCost request.question state ≤
        budget - deliveryCost request.question state := by omega
    simp only [if_neg affordable, if_neg inspection]

/-- The aggregate controller and the independently executed instruction
controller have the same actual public packets at every affordable delivery.
Their unfinished internal states and partial spending are not equated. -/
theorem aggregate_observation_comparison
    (request : Request (Question Action) State Providers Clients) (budget : Nat) (state : State)
    (offered : request.arrival = some state) (deliveryAffordable : deliveryCost request.question state ≤ budget) :
    (inspectReceived presentation deliveryCost request budget state offered deliveryAffordable).responses =
      AssayProbeDelivery.observed ((protocol presentation deliveryCost).test request.question)
        (deliveryCost request.question) ((protocol presentation deliveryCost).inspectionCost request.question)
        request.session request.provider request.client (some state) budget := by
  rw [inspectReceived_responses, AssayProbeDelivery.observed_some]

end Mettapedia.OSLF.Framework.FundedNuInstructionAssays
