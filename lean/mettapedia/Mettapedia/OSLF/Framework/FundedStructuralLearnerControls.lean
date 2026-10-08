import Mettapedia.OSLF.Framework.FundedStructuralIdentification
import Mettapedia.OSLF.Framework.StructuralFundedAssayControls

/-!
# Actual funded learning and its observational boundaries

The environment offers a concrete binary tree. The first test is true of
every candidate; the second separates the finite prior. Eight tokens pay
for both real tests, while seven pay for the first test and the second
delivery without its inspection. Missing offers and incomplete deliveries
leave the candidates unchanged.

A complete survey asks questions derived from the supplied prior, rather
than from the unknown environment. If that prior omits the offered tree,
the complete answers can reject every candidate. With unopened instruments,
distinct candidates remain indistinguishable at every funding level.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedStructuralLearner.Controls

open InstrumentObservations InstrumentObservations.AssayControls FiniteAssayLearner
open Mettapedia.GSLT.Causality ProbeCampaign

def allOpened : Policy Bool := fun constructor => constructor ∈ [false, true]

theorem all_instruments (constructor : Bool) : allOpened constructor := by
  change constructor ∈ [false, true]
  cases constructor <;> decide

def topQuestion : Question (arity := arity) allOpened := ⟨.top, .top⟩

def pairQuestion : Question (arity := arity) allOpened :=
  ⟨pairedFormula, .headed true (fun _ => atomFormula) (all_instruments true)
    (fun _ => .headed false (fun _ => .top) (all_instruments false)
      (fun position => Fin.elim0 position))⟩

def deliveryCost (_ : Question (arity := arity) allOpened) (_ : Tree Bool arity) : Nat := 2

def topRequest : Request (Question (arity := arity) allOpened) (Tree Bool arity) Nat Nat :=
  {question := topQuestion, session := 0, provider := 11, client := 7, arrival := some paired}

def pairRequest : Request (Question (arity := arity) allOpened) (Tree Bool arity) Nat Nat :=
  {question := pairQuestion, session := 1, provider := 12, client := 7, arrival := some paired}

def prior : Finset (Tree Bool arity) := {atom, paired}

def campaign (budget : Nat) :=
  executeCampaign (protocol allOpened deliveryCost) [topRequest, pairRequest] budget

theorem exact_independent_prices :
    quotedPrice (protocol allOpened deliveryCost) topRequest = 3 ∧
      quotedPrice (protocol allOpened deliveryCost) pairRequest = 5 ∧
      totalQuotedPrice (protocol allOpened deliveryCost) [topRequest, pairRequest] = 8 := by
  decide

theorem fully_funded_actual_campaign :
    (campaign 8).completedTests = 2 ∧ (campaign 8).spent = 8 ∧
      (campaign 8).remaining = 0 := by decide

theorem fully_funded_identification :
    learn (prediction allOpened) (campaign 8) prior = {paired} := by decide

theorem seven_tokens_pay_for_an_unanswered_delivery :
    (campaign 7).completedTests = 1 ∧ (campaign 7).spent = 5 ∧
      (campaign 7).remaining = 2 ∧
      learn (prediction allOpened) (campaign 7) prior = prior := by decide

theorem actual_second_delivery_receipt :
    (completedRound (protocol allOpened deliveryCost) pairRequest 4).endpoint =
      AssayProbeDelivery.paidReceived 1 12 7 paired 2 := by decide

theorem offered_truth_without_inspection_cannot_revise :
    prediction allOpened paired pairQuestion = true ∧
      (completedRound (protocol allOpened deliveryCost) pairRequest 4).responses = 0 ∧
      learn (prediction allOpened)
        (executeCampaign (protocol allOpened deliveryCost) [pairRequest] 4) prior = prior := by
  decide

def missingRequest : Request (Question (arity := arity) allOpened) (Tree Bool arity) Nat Nat :=
  {pairRequest with arrival := none}

theorem absent_probe_cannot_reject :
    (executeCampaign (protocol allOpened deliveryCost) [missingRequest] 100).spent = 0 ∧
      learn (prediction allOpened)
        (executeCampaign (protocol allOpened deliveryCost) [missingRequest] 100) prior = prior := by
  decide

def survey (actual : Tree Bool arity) :=
  surveyRequests allOpened all_instruments (11 : Nat) (7 : Nat) actual [atom, paired] 20

theorem actual_survey_affordable : totalQuotedPrice (protocol allOpened deliveryCost) (survey paired) = 8 := by
  decide

theorem survey_identifies_supplied_prior_member :
    learn (prediction allOpened)
      (executeCampaign (protocol allOpened deliveryCost) (survey paired) 8) prior = {paired} := by
  exact supplied_funded_survey_identifies allOpened all_instruments deliveryCost
    (11 : Nat) (7 : Nat) paired [atom, paired] 20 8 (by decide) (by decide)

theorem survey_question_plan_independent_of_offer :
    (survey paired).map Request.question = (survey differentChild).map Request.question := rfl

theorem offered_value_outside_prior : differentChild ∉ prior := by decide

theorem complete_rejection_does_not_mean_missing_environment :
    (executeCampaign (protocol allOpened deliveryCost) (survey differentChild) 8).completedTests = 2 ∧
      learn (prediction allOpened)
        (executeCampaign (protocol allOpened deliveryCost) (survey differentChild) 8) prior = ∅ := by
  decide

def noneOpened : Policy Bool := fun constructor => constructor ∈ ([] : List Bool)

theorem unopened_candidates_have_same_view : view noneOpened atom = view noneOpened paired := by
  simp only [atom, paired, view, noneOpened, List.not_mem_nil, ↓reduceIte]

/-- The negative result covers every independently supplied paid campaign,
not just one controller or one insufficient purse. -/
theorem no_funding_overcomes_unopened_instruments
    (fee : Question (arity := arity) noneOpened → Tree Bool arity → Nat)
    {budget : Nat}
    {requests : List (Request (Question (arity := arity) noneOpened) (Tree Bool arity) Nat Nat)}
    (paid : Campaign (protocol noneOpened fee) budget requests)
    (offers : ∀ request ∈ requests, request.arrival = some paired) :
    atom ∈ learn (prediction noneOpened) paid prior ∧
      paired ∈ learn (prediction noneOpened) paid prior ∧
      learn (prediction noneOpened) paid prior ≠ {paired} := by
  have pairedHeld : paired ∈ prior := by decide
  have atomHeld : atom ∈ prior := by decide
  have actualHeld := actual_candidate_survives noneOpened fee paid prior paired pairedHeld offers
  have hiddenHeld := (same_view_retention noneOpened fee paid prior atomHeld pairedHeld
    unopened_candidates_have_same_view).2 actualHeld
  refine ⟨hiddenHeld, actualHeld, ?_⟩
  intro singleton
  have impossible : atom = paired := Finset.mem_singleton.mp (singleton ▸ hiddenHeld)
  exact (by decide : atom ≠ paired) impossible

end Mettapedia.OSLF.Framework.FundedStructuralLearner.Controls
