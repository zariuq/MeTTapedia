import Mettapedia.GSLT.Causality.PaidProbeCampaign

/-!
# Fully supplied and affordable campaigns complete their actual tests

The quoted campaign price is computed independently from its requests and
offers. If every requested offer exists and their total delivery and test
price fits the initial purse, the completed controller emits one actual
response per request and spends exactly that total. All intermediate purses
are supplied by the retained real occurrence ledgers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

open ComplementaryAssay (verdictOf)

universe q u v w

variable {Questions : Type q} {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def quotedPrice (protocol : Protocol Questions X) (request : Request Questions X Providers Clients) : Nat :=
  match request.arrival with
  | none => 0
  | some value => protocol.deliveryCost request.question value + protocol.inspectionCost request.question value

def totalQuotedPrice (protocol : Protocol Questions X)
    (requests : List (Request Questions X Providers Clients)) : Nat :=
  (requests.map (quotedPrice protocol)).sum

omit [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients] in
theorem totalQuotedPrice_cons (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients)
    (requests : List (Request Questions X Providers Clients)) :
    totalQuotedPrice protocol (request :: requests) = quotedPrice protocol request + totalQuotedPrice protocol requests := rfl

theorem completed_round_price (protocol : Protocol Questions X)
    (request : Request Questions X Providers Clients) (budget : Nat) (value : X)
    (arrives : request.arrival = some value)
    (affordable : protocol.deliveryCost request.question value + protocol.inspectionCost request.question value ≤ budget) :
    (completedRound protocol request budget).responses.card = 1 ∧
      (completedRound protocol request budget).spent = quotedPrice protocol request ∧
      (completedRound protocol request budget).remaining = budget - quotedPrice protocol request := by
  have outputs : (completedRound protocol request budget).responses =
      {(request.session, verdictOf (protocol.test request.question value), request.client, value)} := by
    rw [completedRound_responses, arrives, AssayProbeDelivery.observed_some, if_pos affordable]
  have present : (request.session, verdictOf (protocol.test request.question value), request.client, value) ∈
      (completedRound protocol request budget).responses := by rw [outputs]; exact Multiset.mem_singleton_self _
  obtain ⟨actual, offered, _, _, _, paid⟩ :=
    (completedRound protocol request budget).response_sound _ present
  have same : actual = value := Option.some.inj (offered.symm.trans arrives)
  subst actual
  have quoted : quotedPrice protocol request =
      protocol.deliveryCost request.question value + protocol.inspectionCost request.question value := by
    simp only [quotedPrice, arrives]
  have spent : (completedRound protocol request budget).spent = quotedPrice protocol request := paid.trans quoted.symm
  have conserved := (completedRound protocol request budget).ledger
  refine ⟨by rw [outputs, Multiset.card_singleton], spent, ?_⟩
  omega

/-- Completion is earned from actual path responses and all intermediate
funding, rather than defining the output to be the advertised answer. -/
theorem supplied_affordable_campaign (protocol : Protocol Questions X)
    (requests : List (Request Questions X Providers Clients)) (budget : Nat)
    (supplied : ∀ request ∈ requests, ∃ value, request.arrival = some value)
    (affordable : totalQuotedPrice protocol requests ≤ budget) :
    (executeCampaign protocol requests budget).completedTests = requests.length ∧
      (executeCampaign protocol requests budget).spent = totalQuotedPrice protocol requests ∧
      (executeCampaign protocol requests budget).remaining = budget - totalQuotedPrice protocol requests := by
  induction requests generalizing budget with
  | nil => simp only [executeCampaign, Campaign.completedTests, Campaign.spent, Campaign.remaining,
      totalQuotedPrice, List.map_nil, List.sum_nil, List.length_nil, Nat.sub_zero, and_self]
  | cons request requests inductionHypothesis =>
      obtain ⟨value, arrives⟩ := supplied request List.mem_cons_self
      have firstAffordable : protocol.deliveryCost request.question value +
          protocol.inspectionCost request.question value ≤ budget := by
        rw [totalQuotedPrice_cons] at affordable
        have quoted : quotedPrice protocol request =
            protocol.deliveryCost request.question value + protocol.inspectionCost request.question value := by
          simp only [quotedPrice, arrives]
        omega
      obtain ⟨one, firstPaid, firstRemaining⟩ := completed_round_price protocol request budget value arrives firstAffordable
      have restSupplied : ∀ next ∈ requests, ∃ value, next.arrival = some value :=
        fun next member => supplied next (List.mem_cons_of_mem request member)
      have restAffordable : totalQuotedPrice protocol requests ≤ (completedRound protocol request budget).remaining := by
        rw [totalQuotedPrice_cons] at affordable
        rw [firstRemaining]
        omega
      obtain ⟨restCount, restPaid, restRemaining⟩ := inductionHypothesis
        (completedRound protocol request budget).remaining restSupplied restAffordable
      change (completedRound protocol request budget).responses.card +
          (executeCampaign protocol requests (completedRound protocol request budget).remaining).completedTests =
            (request :: requests).length ∧
        (completedRound protocol request budget).spent +
          (executeCampaign protocol requests (completedRound protocol request budget).remaining).spent =
            totalQuotedPrice protocol (request :: requests) ∧
        (executeCampaign protocol requests (completedRound protocol request budget).remaining).remaining =
          budget - totalQuotedPrice protocol (request :: requests)
      rw [one, restCount, firstPaid, restPaid, totalQuotedPrice_cons, restRemaining, firstRemaining]
      constructor
      · simp only [List.length_cons, Nat.add_comm]
      · constructor
        · rfl
        · omega

end Mettapedia.GSLT.Causality.ProbeCampaign
