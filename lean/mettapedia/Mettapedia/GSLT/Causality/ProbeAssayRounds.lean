import Mettapedia.GSLT.Causality.ProbeAssayExecution

/-!
# Paid probe rounds with independently read responses

A round retains an actual occurrence path, its endpoint and its complete
provider receipt. Its public responses are read from that endpoint. The purse
and spent-token projections give an earned ledger for every supplied prefix,
including prefixes which stop before an affordable interaction.

Questions select separately supplied tests and prices. Requests retain their
offered payloads; supplying an offer is not a theorem about an external
environment or its authority. Responses from these initial markings are
proved sound before the completed controller is used.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

open ResourceInteraction OccurrenceHistory
open ComplementaryAssay (Verdict verdictOf purse)

universe q u v w

structure Protocol (Questions : Type q) (X : Type u) where
  test : Questions → X → Bool
  deliveryCost : Questions → X → Nat
  inspectionCost : Questions → X → Nat

structure Request (Questions : Type q) (X : Type u) (Providers : Type v) (Clients : Type w) where
  question : Questions
  session : Nat
  provider : Providers
  client : Clients
  arrival : Option X

variable {Questions : Type q} {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

abbrev Response (X : Type u) (Clients : Type w) := Nat × Verdict × Clients × X

structure Round (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients) (budget : Nat) where
  endpoint : Multiset (AssayProbeDelivery.Resources X Providers Clients ⊕ Unit)
  path : OccurrencePath
    (AssayProbeDelivery.paid (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).presentation
    (AssayProbeDelivery.initial request.session request.provider request.client request.arrival budget)
    endpoint

namespace Round

variable {protocol : Protocol Questions X} {request : Request Questions X Providers Clients}
variable {budget : Nat}

def responses (round : Round protocol request budget) : Multiset (Response X Clients) :=
  AssayProbeDelivery.outputs (leftPart round.endpoint)

def remaining (round : Round protocol request budget) : Nat := (rightPart round.endpoint).card

def spent (round : Round protocol request budget) : Nat :=
  (((AssayProbeDelivery.paid (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).instanceValuation
      (@AssayProbeDelivery.price X Providers Clients (protocol.test request.question)
        (protocol.deliveryCost request.question) (protocol.inspectionCost request.question))).onPath round.path).card

/-- Every supplied actual prefix conserves its whole paid occurrence ledger. -/
theorem ledger (round : Round protocol request budget) :
    budget = round.remaining + round.spent := by
  have conserved := (AssayProbeDelivery.paid (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).balance_taken
    rightPart rfl rightPart_add
    (@AssayProbeDelivery.price X Providers Clients (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)) (fun firing => by
      change rightPart (marking _ (AssayProbeDelivery.price (protocol.test request.question)
        (protocol.deliveryCost request.question) (protocol.inspectionCost request.question) firing)) =
        AssayProbeDelivery.price (protocol.test request.question) (protocol.deliveryCost request.question)
          (protocol.inspectionCost request.question) firing + rightPart (marking _ (0 : Multiset Unit))
      rw [rightPart_marking, rightPart_marking, add_zero]) round.path
  have initialPurse : rightPart (AssayProbeDelivery.initial request.session request.provider
      request.client request.arrival budget) = purse budget := by
    cases request.arrival <;>
      simp only [AssayProbeDelivery.initial, AssayProbeDelivery.paidOffered, rightPart_marking]
  rw [initialPurse] at conserved
  have counted := congrArg Multiset.card conserved
  simpa only [remaining, spent, Multiset.card_add, purse, Multiset.card_replicate] using counted

theorem remaining_le (round : Round protocol request budget) : round.remaining ≤ budget := by
  have conserved := round.ledger
  omega

theorem absent_is_quiet (round : Round protocol request budget) (absent : request.arrival = none) :
    round.responses = 0 := by
  have path : OccurrencePath
      (AssayProbeDelivery.paid (protocol.test request.question)
        (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).presentation
      (AssayProbeDelivery.initial request.session request.provider request.client none budget)
      round.endpoint := by simpa only [absent] using round.path
  exact (AssayProbeDelivery.absent_offer_prefix (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)
    request.session request.provider request.client budget path).2.1

/-- Every public response has the actual offered value and complementary
guard. Its two interactions were affordable; there is no response from silence. -/
theorem response_sound (round : Round protocol request budget)
    (response : Response X Clients) (present : response ∈ round.responses) :
    ∃ value : X, request.arrival = some value ∧
      response = (request.session, verdictOf (protocol.test request.question value), request.client, value) ∧
      round.responses = {response} ∧
      protocol.deliveryCost request.question value + protocol.inspectionCost request.question value ≤ budget ∧
      round.spent = protocol.deliveryCost request.question value + protocol.inspectionCost request.question value := by
  cases arrival : request.arrival with
  | none =>
    have quiet := round.absent_is_quiet arrival
    rw [quiet] at present
    simp at present
  | some value =>
    have path : OccurrencePath
        (AssayProbeDelivery.paid (protocol.test request.question)
          (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)).presentation
        (AssayProbeDelivery.paidOffered request.session request.provider request.client value budget)
        round.endpoint := by simpa only [AssayProbeDelivery.initial, arrival] using round.path
    rcases AssayProbeDelivery.offered_path_cases (protocol.test request.question)
      (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)
      request.session request.provider request.client value budget path with
      ⟨endpoint, _⟩ | ⟨endpoint, _, _⟩ | ⟨endpoint, _, affordable⟩
    · have quiet : round.responses = 0 := by
        rw [responses, endpoint, AssayProbeDelivery.paidOffered, leftPart_marking,
          AssayProbeDelivery.outputs_offered]
      rw [quiet] at present
      simp at present
    · have quiet : round.responses = 0 := by
        rw [responses, endpoint, AssayProbeDelivery.paidReceived, leftPart_marking,
          AssayProbeDelivery.outputs_received]
      rw [quiet] at present
      simp at present
    · have outputs : round.responses =
          {(request.session, verdictOf (protocol.test request.question value), request.client, value)} := by
        rw [responses, endpoint, AssayProbeDelivery.paidTested, leftPart_marking,
          AssayProbeDelivery.outputs_tested]
      have same := Multiset.mem_singleton.mp (outputs ▸ present)
      refine ⟨value, rfl, same, ?_, affordable, ?_⟩
      · exact outputs.trans (congrArg (fun answer => ({answer} : Multiset (Response X Clients))) same.symm)
      · have remaining : round.remaining =
            (budget - protocol.deliveryCost request.question value) -
              protocol.inspectionCost request.question value := by
          rw [Round.remaining, endpoint, AssayProbeDelivery.paidTested, rightPart_marking]
          exact Multiset.card_replicate _ _
        have conserved := round.ledger
        rw [remaining] at conserved
        omega

theorem response_count_le_one (round : Round protocol request budget) : round.responses.card ≤ 1 := by
  by_cases quiet : round.responses = 0
  · simp only [quiet, Multiset.card_zero, Nat.zero_le]
  · obtain ⟨response, present⟩ := Multiset.exists_mem_of_ne_zero quiet
    obtain ⟨_, _, _, singleton, _, _⟩ := round.response_sound response present
    simp only [singleton, Multiset.card_singleton, le_refl]

/-- A positive per-test lower price bounds the number of completed tests
using the actual spent ledger. Partial deliveries only strengthen the bound. -/
theorem response_price_bound (round : Round protocol request budget) (minimum : Nat)
    (lower : ∀ value, minimum ≤ protocol.deliveryCost request.question value +
      protocol.inspectionCost request.question value) :
    minimum * round.responses.card ≤ round.spent := by
  by_cases quiet : round.responses = 0
  · simp only [quiet, Multiset.card_zero, Nat.mul_zero, Nat.zero_le]
  · obtain ⟨response, present⟩ := Multiset.exists_mem_of_ne_zero quiet
    obtain ⟨value, _, _, singleton, _, spent⟩ := round.response_sound response present
    simpa only [singleton, Multiset.card_singleton, Nat.mul_one, spent] using lower value

end Round

def completedRound (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients) (budget : Nat) : Round protocol request budget :=
  let run := AssayProbeDelivery.execute (protocol.test request.question)
    (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)
    request.session request.provider request.client request.arrival budget
  ⟨run.1, run.2⟩

theorem completedRound_responses (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients) (budget : Nat) :
    (completedRound protocol request budget).responses =
      AssayProbeDelivery.observed (protocol.test request.question)
        (protocol.deliveryCost request.question) (protocol.inspectionCost request.question)
        request.session request.provider request.client request.arrival budget := rfl

end Mettapedia.GSLT.Causality.ProbeCampaign
