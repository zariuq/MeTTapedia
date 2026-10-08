import Mettapedia.GSLT.Causality.PaidProbeCampaign
import Mathlib.Data.Finset.Filter

/-!
# Finite hypothesis revision from actual paid assay responses

A hypothesis predicts a Boolean answer to each declared question. Revision
retains precisely the hypotheses compatible with the public responses of an
actual round. Empty responses leave every candidate intact. A campaign keeps
all provider, payload and occurrence data while this consumer uses its public
projection; public agreement does not reconstruct that retained evidence.

The final version space is characterized by every observed answer. Losing a
previous candidate requires an actual contradictory response. A coherent
candidate survives, and identification requires separately earned separating
observations. These are finite operational observations, without an assumed
identification with a greatest-fixed-point approximation lattice.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteAssayLearner

open Mettapedia.GSLT.Causality ProbeCampaign

universe h q u v w

variable {Hypotheses : Type h} {Questions : Type q} {X : Type u}
variable {Providers : Type v} {Clients : Type w}

def Compatible (prediction : Hypotheses → Questions → Bool) (hypothesis : Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients)) : Prop :=
  ∀ response ∈ responses, prediction hypothesis question = response.2.1.bit

instance compatibleDecidable (prediction : Hypotheses → Questions → Bool) (hypothesis : Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients)) :
    Decidable (Compatible prediction hypothesis question responses) :=
  inferInstanceAs (Decidable (∀ response ∈ responses, prediction hypothesis question = response.2.1.bit))

def revise (prediction : Hypotheses → Questions → Bool) (candidates : Finset Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients)) : Finset Hypotheses :=
  candidates.filter (fun hypothesis => Compatible prediction hypothesis question responses)

theorem revise_mem (prediction : Hypotheses → Questions → Bool) (candidates : Finset Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients)) (hypothesis : Hypotheses) :
    hypothesis ∈ revise prediction candidates question responses ↔
      hypothesis ∈ candidates ∧ Compatible prediction hypothesis question responses :=
  Finset.mem_filter

theorem revise_subset (prediction : Hypotheses → Questions → Bool) (candidates : Finset Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients)) :
    revise prediction candidates question responses ⊆ candidates := Finset.filter_subset _ _

theorem silence_preserves (prediction : Hypotheses → Questions → Bool) (candidates : Finset Hypotheses)
    (question : Questions) : revise prediction candidates question (0 : Multiset (Response X Clients)) = candidates := by
  ext hypothesis
  simp [revise, Compatible]

theorem response_removes (prediction : Hypotheses → Questions → Bool) (candidates : Finset Hypotheses)
    (question : Questions) (responses : Multiset (Response X Clients))
    (hypothesis : Hypotheses) (response : Response X Clients)
    (present : response ∈ responses) (contradiction : prediction hypothesis question ≠ response.2.1.bit) :
    hypothesis ∉ revise prediction candidates question responses := by
  intro retained
  exact contradiction (((revise_mem prediction candidates question responses hypothesis).1 retained).2 response present)

variable {protocol : Protocol Questions X}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

def learn (prediction : Hypotheses → Questions → Bool) :
    {budget : Nat} → {requests : List (Request Questions X Providers Clients)} →
    Campaign protocol budget requests → Finset Hypotheses → Finset Hypotheses
  | _, _, .nil _, candidates => candidates
  | _, request :: _, .cons first rest, candidates =>
      learn prediction rest (revise prediction candidates request.question first.responses)

/-- The operational learner agrees exactly with the entire independently
projected public log, not with a predicted list of successful tests. -/
theorem learn_mem (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses) (hypothesis : Hypotheses) :
    hypothesis ∈ learn prediction campaign candidates ↔ hypothesis ∈ candidates ∧
      ∀ packet ∈ campaign.publicLog, Compatible prediction hypothesis packet.1 packet.2 := by
  induction campaign generalizing candidates with
  | nil _ => simp only [learn, Campaign.publicLog, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
  | @cons budget request requests first rest inductionHypothesis =>
      change hypothesis ∈ learn prediction rest
        (revise prediction candidates request.question first.responses) ↔ _
      rw [inductionHypothesis, revise_mem]
      change (hypothesis ∈ candidates ∧ Compatible prediction hypothesis request.question first.responses) ∧
        (∀ packet ∈ rest.publicLog, Compatible prediction hypothesis packet.1 packet.2) ↔
          hypothesis ∈ candidates ∧
            (∀ packet ∈ (request.question, first.responses) :: rest.publicLog,
              Compatible prediction hypothesis packet.1 packet.2)
      rw [List.forall_mem_cons]
      exact and_assoc

theorem learn_subset (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses) :
    learn prediction campaign candidates ⊆ candidates := by
  intro hypothesis retained
  exact ((learn_mem prediction campaign candidates hypothesis).1 retained).1

/-- A loss of a previously held hypothesis has an actual finite refutation
in the projected response log. Absence and underfunding cannot supply it. -/
theorem removed_iff_counterexample (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses)
    (hypothesis : Hypotheses) (initial : hypothesis ∈ candidates) :
    hypothesis ∉ learn prediction campaign candidates ↔
      ∃ packet ∈ campaign.publicLog, ∃ response ∈ packet.2,
        prediction hypothesis packet.1 ≠ response.2.1.bit := by
  classical
  rw [learn_mem, not_and]
  simp only [initial, true_implies, Compatible]
  push Not
  rfl

theorem coherent_candidate_survives (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses)
    (hypothesis : Hypotheses) (initial : hypothesis ∈ candidates)
    (agrees : ∀ packet ∈ campaign.publicLog, Compatible prediction hypothesis packet.1 packet.2) :
    hypothesis ∈ learn prediction campaign candidates :=
  (learn_mem prediction campaign candidates hypothesis).2 ⟨initial, agrees⟩

/-- Independent predictions of the supplied offers earn compatibility with
every actual reply, including independently supplied unfinished prefixes. -/
theorem offered_candidate_survives (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses)
    (hypothesis : Hypotheses) (initial : hypothesis ∈ candidates)
    (predictsOffers : ∀ request ∈ requests, ∀ value, request.arrival = some value →
      prediction hypothesis request.question = protocol.test request.question value) :
    hypothesis ∈ learn prediction campaign candidates := by
  induction campaign generalizing candidates with
  | nil _ => exact initial
  | @cons budget request requests first rest inductionHypothesis =>
      have firstCompatible : Compatible prediction hypothesis request.question first.responses := by
        intro response present
        obtain ⟨value, offered, same, _, _, _⟩ := first.response_sound response present
        rw [same, ComplementaryAssay.verdictOf_bit]
        exact predictsOffers request List.mem_cons_self value offered
      have retained : hypothesis ∈ revise prediction candidates request.question first.responses :=
        (revise_mem prediction candidates request.question first.responses hypothesis).2 ⟨initial, firstCompatible⟩
      exact inductionHypothesis _ retained (fun next member value arrives =>
        predictsOffers next (List.mem_cons_of_mem request member) value arrives)

/-- Identification is earned only when the actual answered questions
separate the coherent candidate from every other initially held candidate. -/
theorem identified_by_responses (prediction : Hypotheses → Questions → Bool)
    {budget : Nat} {requests : List (Request Questions X Providers Clients)}
    (campaign : Campaign protocol budget requests) (candidates : Finset Hypotheses)
    (actual : Hypotheses) (initial : actual ∈ candidates)
    (agrees : ∀ packet ∈ campaign.publicLog, Compatible prediction actual packet.1 packet.2)
    (separates : ∀ hypothesis ∈ candidates, hypothesis ≠ actual →
      ∃ packet ∈ campaign.publicLog, ∃ response ∈ packet.2,
        prediction hypothesis packet.1 ≠ response.2.1.bit) :
    learn prediction campaign candidates = {actual} := by
  classical
  ext hypothesis
  constructor
  · intro retained
    have original := ((learn_mem prediction campaign candidates hypothesis).1 retained).1
    by_cases same : hypothesis = actual
    · exact Finset.mem_singleton.mpr same
    · have removed := (removed_iff_counterexample prediction campaign candidates hypothesis original).2
        (separates hypothesis original same)
      exact False.elim (removed retained)
  · intro member
    have same := Finset.mem_singleton.mp member
    subst hypothesis
    exact coherent_candidate_survives prediction campaign candidates actual initial agrees

end Mettapedia.OSLF.Framework.FiniteAssayLearner
