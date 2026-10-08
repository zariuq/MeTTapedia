import Mettapedia.OSLF.Framework.FundedStructuralLearner
import Mettapedia.OSLF.Framework.InstrumentShapeTests
import Mettapedia.GSLT.Causality.ProbeCampaignCompletion

/-!
# Complete funded surveys of an independently supplied finite prior

The survey asks the shape question of every supplied candidate, with a
separate session at every list occurrence. It does not choose its questions
by consulting the received environment tree. Snapshot offers are supplied
separately and explicitly.

For a complete instrument policy, the candidate's own shape is a separating
test. If the prior contains the offered tree and the entire quoted campaign
is affordable, the actual paid controller identifies that tree uniquely.
Partial instruments and incomplete funding have their separate limits; the
theorem neither enlarges the prior nor answers questions beyond the admitted
instrument interface.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedStructuralLearner

open InstrumentObservations FiniteAssayLearner
open Mettapedia.GSLT.Causality ProbeCampaign

universe u v w

variable {Symbols : Type u} {arity : Symbols → Nat}

def shapeQuestion (opened : Policy Symbols) (complete : ∀ constructor, opened constructor)
    (hypothesis : Tree Symbols arity) : Question (arity := arity) opened :=
  ⟨shapeFormula hypothesis, shapeFormula_admitted opened complete hypothesis⟩

variable {Providers : Type v} {Clients : Type w}

def surveyRequests (opened : Policy Symbols) (complete : ∀ constructor, opened constructor)
    (provider : Providers) (client : Clients) (actual : Tree Symbols arity) :
    List (Tree Symbols arity) → Nat →
      List (Request (Question (arity := arity) opened) (Tree Symbols arity) Providers Clients)
  | [], _ => []
  | hypothesis :: hypotheses, session =>
      {question := shapeQuestion opened complete hypothesis, session := session,
        provider := provider, client := client, arrival := some actual} ::
      surveyRequests opened complete provider client actual hypotheses (session + 1)

theorem survey_offers (opened : Policy Symbols) (complete : ∀ constructor, opened constructor)
    (provider : Providers) (client : Clients) (actual : Tree Symbols arity)
    (hypotheses : List (Tree Symbols arity)) (session : Nat) :
    ∀ request ∈ surveyRequests opened complete provider client actual hypotheses session,
      request.arrival = some actual := by
  induction hypotheses generalizing session with
  | nil => intro request member; simp [surveyRequests] at member
  | cons hypothesis hypotheses inductionHypothesis =>
      intro request member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact inductionHypothesis (session + 1) request later

theorem survey_asks_every_candidate (opened : Policy Symbols) (complete : ∀ constructor, opened constructor)
    (provider : Providers) (client : Clients) (actual : Tree Symbols arity)
    (hypotheses : List (Tree Symbols arity)) (session : Nat)
    (hypothesis : Tree Symbols arity) (held : hypothesis ∈ hypotheses) :
    ∃ request ∈ surveyRequests opened complete provider client actual hypotheses session,
      request.question = shapeQuestion opened complete hypothesis := by
  induction hypotheses generalizing session with
  | nil => simp at held
  | cons first hypotheses inductionHypothesis =>
      rcases List.mem_cons.mp held with rfl | later
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨request, member, question⟩ := inductionHypothesis (session + 1) later
        exact ⟨request, List.mem_cons_of_mem _ member, question⟩

variable [DecidableEq Symbols] [DecidableEq Providers] [DecidableEq Clients]

/-- A full actual campaign identifies the offered tree once every initially
held candidate has its independently constructed shape question in the plan. -/
theorem complete_shape_campaign_identifies (opened : Policy Symbols)
    (complete : ∀ constructor, opened constructor)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat)
    {budget : Nat} {requests : List (Request (Question (arity := arity) opened)
      (Tree Symbols arity) Providers Clients)}
    (campaign : Campaign (protocol opened deliveryCost) budget requests)
    (candidates : Finset (Tree Symbols arity)) (actual : Tree Symbols arity)
    (initial : actual ∈ candidates)
    (offers : ∀ request ∈ requests, request.arrival = some actual)
    (finished : campaign.completedTests = requests.length)
    (covers : ∀ hypothesis ∈ candidates, ∃ request ∈ requests,
      request.question = shapeQuestion opened complete hypothesis) :
    learn (prediction opened) campaign candidates = {actual} := by
  have actualRetained := actual_candidate_survives opened deliveryCost campaign candidates actual initial offers
  have actualCompatible := ((learn_mem (prediction opened) campaign candidates actual).1 actualRetained).2
  apply identified_by_responses (prediction opened) campaign candidates actual initial actualCompatible
  intro hypothesis held different
  obtain ⟨request, requested, question⟩ := covers hypothesis held
  obtain ⟨packet, member, sameQuestion, one⟩ := campaign.completed_member_responded finished request requested
  have notQuiet : packet.2 ≠ 0 := by
    intro quiet
    rw [quiet, Multiset.card_zero] at one
    omega
  obtain ⟨response, present⟩ := Multiset.exists_mem_of_ne_zero notQuiet
  refine ⟨packet, member, response, present, ?_⟩
  have actualAnswer := actualCompatible packet member response present
  rw [sameQuestion, question] at actualAnswer ⊢
  have selfAnswer : prediction opened hypothesis (shapeQuestion opened complete hypothesis) = true :=
    shapeFormula_self hypothesis
  have otherAnswer : prediction opened actual (shapeQuestion opened complete hypothesis) = false := by
    change evaluate (shapeFormula hypothesis) actual = false
    rw [shapeFormula_readout, decide_eq_false_iff_not]
    exact different
  rw [otherAnswer] at actualAnswer
  rw [selfAnswer]
  exact fun contrary => Bool.false_ne_true (actualAnswer.trans contrary.symm)

/-- The complete source-independent survey receives every offered reply
through the real paid protocol before using its separating readouts. -/
theorem supplied_funded_survey_identifies (opened : Policy Symbols)
    (complete : ∀ constructor, opened constructor)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat)
    (provider : Providers) (client : Clients) (actual : Tree Symbols arity)
    (hypotheses : List (Tree Symbols arity)) (session budget : Nat)
    (initial : actual ∈ hypotheses)
    (affordable : totalQuotedPrice (protocol opened deliveryCost)
      (surveyRequests opened complete provider client actual hypotheses session) ≤ budget) :
    learn (prediction opened)
      (executeCampaign (protocol opened deliveryCost)
        (surveyRequests opened complete provider client actual hypotheses session) budget)
      hypotheses.toFinset = {actual} := by
  have offers := survey_offers opened complete provider client actual hypotheses session
  have finished := (supplied_affordable_campaign (protocol opened deliveryCost)
    (surveyRequests opened complete provider client actual hypotheses session) budget
    (fun request member => ⟨actual, offers request member⟩) affordable).1
  apply complete_shape_campaign_identifies opened complete deliveryCost _ hypotheses.toFinset actual
    (List.mem_toFinset.mpr initial) offers finished
  intro hypothesis held
  exact survey_asks_every_candidate opened complete provider client actual hypotheses session
    hypothesis (List.mem_toFinset.mp held)

end Mettapedia.OSLF.Framework.FundedStructuralLearner
