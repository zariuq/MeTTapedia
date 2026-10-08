import Mettapedia.GSLT.Causality.ProbeAssayRounds

/-!
# Sequential campaigns retaining actual paid probe paths

Every new round receives exactly the remaining purse of the previous one.
The campaign retains each complete occurrence path and endpoint rather than
only a list of verdicts. Its public log is projected from those endpoints;
the total purse law and the paid bound on completed tests follow from the
individual actual ledgers.

These are sequential protocol rounds with explicitly supplied initial
requests and offers. No claim identifies their setup with an uncharged
rewrite of one closed world, or supplies an external environment response.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbeCampaign

universe q u v w

variable {Questions : Type q} {X : Type u} {Providers : Type v} {Clients : Type w}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

inductive Campaign (protocol : Protocol Questions X) :
    Nat → List (Request Questions X Providers Clients) → Type (max q u v w) where
  | nil (budget : Nat) : Campaign protocol budget []
  | cons {budget : Nat} {request : Request Questions X Providers Clients}
      {requests : List (Request Questions X Providers Clients)}
      (first : Round protocol request budget)
      (rest : Campaign protocol first.remaining requests) :
      Campaign protocol budget (request :: requests)

namespace Campaign

variable {protocol : Protocol Questions X}

def remaining : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → Nat
  | _, _, .nil budget => budget
  | _, _, .cons _ rest => remaining rest

def spent : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → Nat
  | _, _, .nil _ => 0
  | _, _, .cons first rest => first.spent + spent rest

def publicLog : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → List (Questions × Multiset (Response X Clients))
  | _, _, .nil _ => []
  | _, request :: _, .cons first rest =>
      (request.question, first.responses) :: publicLog rest

def completedTests : {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → Nat
  | _, _, .nil _ => 0
  | _, _, .cons first rest => first.responses.card + completedTests rest

theorem ledger {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) :
    budget = campaign.remaining + campaign.spent := by
  induction campaign with
  | nil budget => simp only [remaining, spent, Nat.add_zero]
  | cons first rest inductionHypothesis =>
      have firstLedger := first.ledger
      change _ = rest.remaining + (first.spent + rest.spent)
      omega

theorem remaining_le {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) : campaign.remaining ≤ budget := by
  have conserved := campaign.ledger
  omega

theorem publicLog_length {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) : campaign.publicLog.length = requests.length := by
  induction campaign with
  | nil _ => rfl
  | cons first rest inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

theorem completedTests_le_requests {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) : campaign.completedTests ≤ requests.length := by
  induction campaign with
  | nil _ => exact le_rfl
  | cons first rest inductionHypothesis =>
      have bounded := first.response_count_le_one
      change first.responses.card + rest.completedTests ≤ _ + 1
      omega

/-- Full completion supplies an actually answered public packet for every
requested question, including repeated requests with the same question. -/
theorem completed_member_responded {budget : Nat}
    {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests)
    (complete : campaign.completedTests = requests.length)
    (request : Request Questions X Providers Clients) (requested : request ∈ requests) :
    ∃ packet ∈ campaign.publicLog, packet.1 = request.question ∧ packet.2.card = 1 := by
  induction campaign with
  | nil _ => simp at requested
  | @cons budget firstRequest requests first rest inductionHypothesis =>
      have firstBound := first.response_count_le_one
      have restBound := rest.completedTests_le_requests
      have whole : first.responses.card + rest.completedTests = requests.length + 1 := complete
      have one : first.responses.card = 1 := by omega
      have restComplete : rest.completedTests = requests.length := by omega
      rcases List.mem_cons.mp requested with same | later
      · subst request
        exact ⟨(firstRequest.question, first.responses), List.mem_cons_self, rfl, one⟩
      · obtain ⟨packet, member, question, answered⟩ := inductionHypothesis restComplete later
        exact ⟨packet, List.mem_cons_of_mem _ member, question, answered⟩

/-- Even independently supplied prefixes obey the completed-test bound.
Waiting rounds and partial deliveries cannot create a free completed test. -/
theorem paid_test_bound {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (minimum : Nat)
    (lower : ∀ question value, minimum ≤ protocol.deliveryCost question value +
      protocol.inspectionCost question value) :
    minimum * campaign.completedTests ≤ campaign.spent := by
  induction campaign with
  | nil _ => exact le_rfl
  | cons first rest inductionHypothesis =>
      have firstBound := first.response_price_bound minimum (lower _)
      change minimum * (first.responses.card + rest.completedTests) ≤ first.spent + rest.spent
      rw [Nat.mul_add]
      exact Nat.add_le_add firstBound inductionHypothesis

theorem paid_branching_bound {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (minimum : Nat)
    (lower : ∀ question value, minimum ≤ protocol.deliveryCost question value +
      protocol.inspectionCost question value) :
    minimum * campaign.completedTests ≤ budget := by
  have paid := campaign.paid_test_bound minimum lower
  have conserved := campaign.ledger
  omega

theorem paid_branching_division {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (minimum : Nat) (positive : 0 < minimum)
    (lower : ∀ question value, minimum ≤ protocol.deliveryCost question value +
      protocol.inspectionCost question value) :
    campaign.completedTests ≤ budget / minimum := by
  apply (Nat.le_div_iff_mul_le positive).mpr
  simpa only [Nat.mul_comm] using campaign.paid_branching_bound minimum lower

end Campaign

/-- The controller stores the real funded occurrence path at every round. -/
def executeCampaign (protocol : Protocol Questions X) :
    (requests : List (Request Questions X Providers Clients)) → (budget : Nat) →
      Campaign protocol budget requests
  | [], budget => .nil budget
  | request :: requests, budget =>
      let first := completedRound protocol request budget
      .cons first (executeCampaign protocol requests first.remaining)

end Mettapedia.GSLT.Causality.ProbeCampaign
