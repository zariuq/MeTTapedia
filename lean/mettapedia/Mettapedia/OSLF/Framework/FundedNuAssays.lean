import Mettapedia.Logic.ModalNuUnfoldings
import Mettapedia.GSLT.Causality.ProbeAssayRounds

/-!
# Paid tests of actual greatest-fixed-point unfoldings

A question retains its positive body and unfolding index. Its guard and price
come from an independently computed complete inspection. Public responses are
read from actual probe-delivery occurrence paths, retaining the received state,
provider receipt, session, client and paid ledger.

A refuting response refutes the original greatest fixed point at the received
state. A confirming response certifies its actual approximation. On a finite
state carrier, the earned cardinality bound upgrades that confirmation to the
original hypothesis. Funding or a successful shallow test alone does not.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuAssays

open Mettapedia.Logic.ModalMuCalculus
open Inspection Unfolding
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

universe u v w z

variable {State : Type u} {Action : Type v}

abbrev Question (Action : Type v) := PositiveHMLBody Action × Nat

def emptyEnvironment : BooleanEnv State 0 := Fin.elim0

theorem emptyEnvironment_read : (emptyEnvironment (State := State)).toEnv = Env.empty := by
  funext impossible
  exact Fin.elim0 impossible

def protocol (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat) : Protocol (Question Action) State where
  test question state :=
    (inspect presentation (question.1.atStage question.2)
      (question.1.stage_admitted question.2) emptyEnvironment state).1
  deliveryCost := deliveryCost
  inspectionCost question state :=
    (inspect presentation (question.1.atStage question.2)
      (question.1.stage_admitted question.2) emptyEnvironment state).2

theorem test_truth (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat) (question : Question Action) (state : State) :
    (protocol presentation deliveryCost).test question state = true ↔
      satisfies presentation.toLTS Env.empty (question.1.atStage question.2) state := by
  have checked := inspect_truth presentation (question.1.atStage question.2)
    (question.1.stage_admitted question.2) emptyEnvironment state
  rw [emptyEnvironment_read] at checked
  exact checked

theorem test_falsehood (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat) (question : Question Action) (state : State) :
    (protocol presentation deliveryCost).test question state = false ↔
      ¬ satisfies presentation.toLTS Env.empty (question.1.atStage question.2) state := by
  have checked := inspect_falsehood presentation (question.1.atStage question.2)
    (question.1.stage_admitted question.2) emptyEnvironment state
  rw [emptyEnvironment_read] at checked
  exact checked

/-- The certificate is specified by the original modal semantics, separately
from the procedure computing the assay's Boolean guard. -/
def StageCertificate (presentation : SuccessorPresentation State Action)
    (question : Question Action) (branch : Verdict) (state : State) : Prop :=
  match branch with
  | .confirm => satisfies presentation.toLTS Env.empty (question.1.atStage question.2) state
  | .refute => ¬ satisfies presentation.toLTS Env.empty (question.1.atStage question.2) state

theorem tested_certificate (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat) (question : Question Action) (state : State) :
    StageCertificate presentation question
      (verdictOf ((protocol presentation deliveryCost).test question state)) state := by
  cases answer : (protocol presentation deliveryCost).test question state with
  | false => exact (test_falsehood presentation deliveryCost question state).1 answer
  | true => exact (test_truth presentation deliveryCost question state).1 answer

theorem inspection_price_positive (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat) (question : Question Action) (state : State) :
    0 < (protocol presentation deliveryCost).inspectionCost question state :=
  inspection_positive presentation (question.1.atStage question.2)
    (question.1.stage_admitted question.2) emptyEnvironment state

variable {Providers : Type w} {Clients : Type z}
variable [DecidableEq State] [DecidableEq Providers] [DecidableEq Clients]

/-- Any actual response retains the exact supplied offer and earned modal
certificate, together with the complete ledger of both paid interactions. -/
theorem response_certificate (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    {request : Request (Question Action) State Providers Clients} {budget : Nat}
    (round : Round (protocol presentation deliveryCost) request budget)
    (response : Response State Clients) (present : response ∈ round.responses) :
    ∃ state, request.arrival = some state ∧
      response = (request.session,
        verdictOf ((protocol presentation deliveryCost).test request.question state),
        request.client, state) ∧
      StageCertificate presentation request.question
        (verdictOf ((protocol presentation deliveryCost).test request.question state)) state ∧
      round.responses = {response} ∧
      round.spent = deliveryCost request.question state +
        (protocol presentation deliveryCost).inspectionCost request.question state ∧
      round.spent ≤ budget := by
  obtain ⟨state, offered, readout, singleton, affordable, spent⟩ :=
    round.response_sound response present
  exact ⟨state, offered, readout, tested_certificate presentation deliveryCost request.question state,
    singleton, spent, spent ▸ affordable⟩

theorem received_refutation (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    {request : Request (Question Action) State Providers Clients} {budget : Nat}
    (round : Round (protocol presentation deliveryCost) request budget) (state : State)
    (present : (request.session, Verdict.refute, request.client, state) ∈ round.responses) :
    ¬ satisfies presentation.toLTS Env.empty (.nu request.question.1.body) state := by
  obtain ⟨received, _, same, _, _, _⟩ := round.response_sound _ present
  have fields := Prod.mk.inj same
  have values := Prod.mk.inj fields.2
  have contents := Prod.mk.inj values.2
  have stateSame : state = received := contents.2
  have branch : verdictOf ((protocol presentation deliveryCost).test request.question received) =
      Verdict.refute := values.1.symm
  have result := tested_certificate presentation deliveryCost request.question received
  rw [branch] at result
  exact stateSame ▸ refuted_stage_refutes_original presentation.toLTS request.question.1
    request.question.2 received result

theorem received_finite_confirmation [Finite State]
    (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    {request : Request (Question Action) State Providers Clients} {budget : Nat}
    (round : Round (protocol presentation deliveryCost) request budget) (state : State)
    (enough : Nat.card State ≤ request.question.2)
    (present : (request.session, Verdict.confirm, request.client, state) ∈ round.responses) :
    satisfies presentation.toLTS Env.empty (.nu request.question.1.body) state := by
  obtain ⟨received, _, same, _, _, _⟩ := round.response_sound _ present
  have fields := Prod.mk.inj same
  have values := Prod.mk.inj fields.2
  have contents := Prod.mk.inj values.2
  have stateSame : state = received := contents.2
  have branch : verdictOf ((protocol presentation deliveryCost).test request.question received) =
      Verdict.confirm := values.1.symm
  have result := tested_certificate presentation deliveryCost request.question received
  rw [branch] at result
  exact stateSame ▸ (finite_stage_equals_original presentation.toLTS request.question.1
    request.question.2 enough received).1 result

theorem round_test_bound (presentation : SuccessorPresentation State Action)
    (deliveryCost : Question Action → State → Nat)
    {request : Request (Question Action) State Providers Clients} {budget : Nat}
    (round : Round (protocol presentation deliveryCost) request budget) :
    round.responses.card ≤ budget := by
  have bound := round.response_price_bound 1 (fun state => by
    change 1 ≤ deliveryCost request.question state +
      (protocol presentation deliveryCost).inspectionCost request.question state
    have positive := inspection_price_positive presentation deliveryCost request.question state
    omega)
  have ledger := round.ledger
  simp only [Nat.one_mul] at bound
  omega

end Mettapedia.OSLF.Framework.FundedNuAssays
