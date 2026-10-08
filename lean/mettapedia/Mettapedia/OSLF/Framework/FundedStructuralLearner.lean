import Mettapedia.OSLF.Framework.FiniteAssayLearner
import Mettapedia.OSLF.Framework.InstrumentTestExecution
import Mettapedia.OSLF.Framework.InstrumentTreeDecision

/-!
# Paid structural learning with an admitted instrument ceiling

Every question retains its actual structural formula and instrument admission.
Independent model predictions use structural evaluation; actual responses use
the separately computed inspection. Their earned comparison keeps a correctly
predicted offered tree in the finite version space.

The positive inspection price is computed from every visited test node.
Therefore actual completed tests are bounded by the initial purse. All
predictions remain invariant under the partial instrument view, giving an
observational limit even when arbitrary funding is available.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedStructuralLearner

open InstrumentObservations FiniteAssayLearner
open Mettapedia.GSLT.Causality ProbeCampaign

universe u v w

variable {Symbols : Type u} {arity : Symbols → Nat}

abbrev Question (opened : Policy Symbols) :=
  {formula : Formula Symbols arity // AdmittedFormula opened formula}

variable [DecidableEq Symbols]

def protocol (opened : Policy Symbols)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat) :
    Protocol (Question (arity := arity) opened) (Tree Symbols arity) where
  test question tree := (inspect question.val tree).1
  deliveryCost := deliveryCost
  inspectionCost question tree := (inspect question.val tree).2

def prediction (opened : Policy Symbols) (hypothesis : Tree Symbols arity)
    (question : Question (arity := arity) opened) : Bool := evaluate question.val hypothesis

theorem inspection_positive (formula : Formula Symbols arity) (tree : Tree Symbols arity) :
    0 < (inspect formula tree).2 := by
  rw [inspect_work]
  cases formula with
  | top => exact Nat.zero_lt_one
  | neg body => change 0 < 1 + traversalWork body tree; omega
  | conj first second => change 0 < 1 + traversalWork first tree + traversalWork second tree; omega
  | headed constructor formulas =>
      cases tree with
      | node other arguments =>
          unfold traversalWork
          split_ifs <;> omega

variable {Providers : Type v} {Clients : Type w}
variable [DecidableEq Providers] [DecidableEq Clients]

/-- The performed inspection, not formula depth or an external speed claim,
earns a strictly positive lower price for every completed structural test. -/
theorem campaign_test_bound (opened : Policy Symbols)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat)
    {budget : Nat} {requests : List (Request (Question (arity := arity) opened)
      (Tree Symbols arity) Providers Clients)}
    (campaign : Campaign (protocol opened deliveryCost) budget requests) :
    campaign.completedTests ≤ budget := by
  have paid := campaign.paid_branching_bound 1 (fun question value => by
    change 1 ≤ deliveryCost question value + (inspect question.val value).2
    have positive := inspection_positive question.val value
    omega)
  simpa only [Nat.one_mul] using paid

/-- Every original tree candidate which predicts the supplied responses
survives actual prefixes, without requiring that those prefixes complete. -/
theorem actual_candidate_survives (opened : Policy Symbols)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat)
    {budget : Nat} {requests : List (Request (Question (arity := arity) opened)
      (Tree Symbols arity) Providers Clients)}
    (campaign : Campaign (protocol opened deliveryCost) budget requests)
    (candidates : Finset (Tree Symbols arity)) (actual : Tree Symbols arity)
    (initial : actual ∈ candidates)
    (offers : ∀ request ∈ requests, request.arrival = some actual) :
    actual ∈ learn (prediction opened) campaign candidates := by
  apply offered_candidate_survives (prediction opened) campaign candidates actual initial
  intro request member value arrives
  have same : value = actual := Option.some.inj (arrives.symm.trans (offers request member))
  subst value
  exact (congrArg Prod.fst (inspect_readout request.question.val actual)).symm

theorem same_view_predictions (opened : Policy Symbols) {first second : Tree Symbols arity}
    (same : view opened first = view opened second) (question : Question (arity := arity) opened) :
    prediction opened first question = prediction opened second question :=
  evaluate_same_view opened question.val question.property same

/-- Admitted instruments cannot separate candidates hidden by the same
partial view, regardless of which funded campaign is supplied. -/
theorem same_view_retention (opened : Policy Symbols)
    (deliveryCost : Question (arity := arity) opened → Tree Symbols arity → Nat)
    {budget : Nat} {requests : List (Request (Question (arity := arity) opened)
      (Tree Symbols arity) Providers Clients)}
    (campaign : Campaign (protocol opened deliveryCost) budget requests)
    (candidates : Finset (Tree Symbols arity)) {first second : Tree Symbols arity}
    (firstHeld : first ∈ candidates) (secondHeld : second ∈ candidates)
    (same : view opened first = view opened second) :
    first ∈ learn (prediction opened) campaign candidates ↔
      second ∈ learn (prediction opened) campaign candidates := by
  rw [learn_mem, learn_mem]
  simp only [firstHeld, secondHeld, true_and]
  have compatible : ∀ (question : Question (arity := arity) opened)
      (responses : Multiset (Response (Tree Symbols arity) Clients)),
      Compatible (prediction opened) first question responses ↔
        Compatible (prediction opened) second question responses := by
    intro question responses
    unfold Compatible
    rw [same_view_predictions opened same question]
  simp only [compatible]

end Mettapedia.OSLF.Framework.FundedStructuralLearner
