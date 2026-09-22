import Mettapedia.Ethics.CommunicationLanguage
import Mettapedia.GSLT.Core.ObservedBisimulation

/-!
# Honest and true communication as observer-relative behavioral concepts

The Formal Ethics Ontology distinguishes:

* honest communication: the communicator believes the message to be true
  during the communication; and
* true communication: the message is in fact true during the communication.

The operational semantics of one communication episode is the authored
`communicationLanguage`, and every result below is stated over the GSLT the OSLF
construction generates from it.  Belief and truth are arguments of an episode
that its rewrites carry forward unchanged while its phase advances.  The full
observer can inspect both; the outcome observer can inspect truth and completion
but not belief.

The positive results show that both concepts are saturated unions of classes
for a sufficiently discriminating observer. The negative result shows that
honesty is not a concept on the outcome-only quotient: an honest true message
and a dishonest true message are outcome-bisimilar. This is a precise boundary
on the claim that behavioral equivalence classes form a basis for ontology.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalCommunicationBisimulation

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Ethics.CommunicationLanguage

/-! ## Source concepts -/

/-- The communicator believes the message to be true throughout the episode. -/
def HonestCommunication (term : Pattern) : Prop :=
  ∃ phase truth, term = episode phase yes truth

/-- The message is true throughout the episode. -/
def TrueCommunication (term : Pattern) : Prop :=
  ∃ phase belief, term = episode phase belief yes

/-- The episode has completed. -/
def CompletedCommunication (term : Pattern) : Prop :=
  ∃ belief truth, term = episode completed belief truth

theorem honestCommunication_episode_iff (phase belief truth : Pattern) :
    HonestCommunication (episode phase belief truth) ↔ belief = yes := by
  constructor
  · rintro ⟨_, _, same⟩
    exact (episode_injective same).2.1
  · rintro rfl
    exact ⟨phase, truth, rfl⟩

theorem trueCommunication_episode_iff (phase belief truth : Pattern) :
    TrueCommunication (episode phase belief truth) ↔ truth = yes := by
  constructor
  · rintro ⟨_, _, same⟩
    exact (episode_injective same).2.2
  · rintro rfl
    exact ⟨phase, belief, rfl⟩

theorem completedCommunication_episode_iff (phase belief truth : Pattern) :
    CompletedCommunication (episode phase belief truth) ↔ phase = completed := by
  constructor
  · rintro ⟨_, _, same⟩
    exact (episode_injective same).1
  · rintro rfl
    exact ⟨belief, truth, rfl⟩

/-! ## Full and outcome observers -/

inductive FullAtom : Type
  | beliefTrue
  | messageTrue
  | completed
  deriving DecidableEq, Repr

def fullObserved : ObservedGSLT communicationTheory where
  Atom := FullAtom
  observes atom term :=
    match atom with
    | .beliefTrue => HonestCommunication term
    | .messageTrue => TrueCommunication term
    | .completed => CompletedCommunication term

inductive OutcomeAtom : Type
  | messageTrue
  | completed
  deriving DecidableEq, Repr

def outcomeObserved : ObservedGSLT communicationTheory where
  Atom := OutcomeAtom
  observes atom term :=
    match atom with
    | .messageTrue => TrueCommunication term
    | .completed => CompletedCommunication term

/-! ## The outcome bisimulation -/

/-- The outcome observer retains phase and message truth but forgets the
communicator's belief. -/
def SameOutcome (left right : Pattern) : Prop :=
  left = right ∨
    ∃ phase belief belief' truth, left = episode phase belief truth ∧ right = episode phase belief' truth

theorem SameOutcome.symm {left right : Pattern}
    (same : SameOutcome left right) : SameOutcome right left := by
  rcases same with rfl | ⟨phase, belief, belief', truth, rfl, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨phase, belief', belief, truth, rfl, rfl⟩

theorem sameOutcome_forward {left right next : Pattern}
    (same : SameOutcome left right)
    (step : communicationTheory.Step left next) :
    ∃ rightNext, communicationTheory.Step right rightNext ∧
      SameOutcome next rightNext := by
  rcases same with rfl | ⟨phase, belief, belief', truth, rfl, rfl⟩
  · exact ⟨next, step, .inl rfl⟩
  · obtain ⟨stepBelief, stepTruth, (⟨source, rfl⟩ | ⟨source, rfl⟩)⟩ := (step_iff _ _).mp step
    · obtain ⟨rfl, rfl, rfl⟩ := episode_injective source
      exact ⟨episode communicating belief' truth, start_step belief' truth,
        .inr ⟨communicating, belief, belief', truth, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl, rfl⟩ := episode_injective source
      exact ⟨episode completed belief' truth, finish_step belief' truth,
        .inr ⟨completed, belief, belief', truth, rfl, rfl⟩⟩

theorem sameOutcome_is_step_bisimulation :
    communicationTheory.IsBisimulation SameOutcome := by
  constructor
  · intro left right same next step
    exact sameOutcome_forward same step
  · intro left right same next step
    rcases sameOutcome_forward same.symm step with
      ⟨leftNext, leftStep, nextSame⟩
    exact ⟨leftNext, leftStep, nextSame.symm⟩

theorem sameOutcome_preserves_outcome_atoms
    {left right : Pattern} (same : SameOutcome left right)
    (atom : OutcomeAtom) :
    outcomeObserved.observes atom left ↔
      outcomeObserved.observes atom right := by
  rcases same with rfl | ⟨phase, belief, belief', truth, rfl, rfl⟩
  · exact Iff.rfl
  · cases atom
    · change TrueCommunication _ ↔ TrueCommunication _
      rw [trueCommunication_episode_iff, trueCommunication_episode_iff]
    · change CompletedCommunication _ ↔ CompletedCommunication _
      rw [completedCommunication_episode_iff, completedCommunication_episode_iff]

theorem sameOutcome_is_observed_bisimulation :
    outcomeObserved.IsBisimulation SameOutcome := by
  refine ⟨sameOutcome_is_step_bisimulation, ?_⟩
  intro left right same atom
  exact sameOutcome_preserves_outcome_atoms same atom

/-! ## Positive and negative ontology results -/

theorem honest_saturated_full :
    fullObserved.Saturated HonestCommunication := by
  intro left right bisimilar
  exact fullObserved.observation_invariant bisimilar .beliefTrue

theorem true_saturated_full :
    fullObserved.Saturated TrueCommunication := by
  intro left right bisimilar
  exact fullObserved.observation_invariant bisimilar .messageTrue

theorem true_saturated_outcome :
    outcomeObserved.Saturated TrueCommunication := by
  intro left right bisimilar
  exact outcomeObserved.observation_invariant bisimilar .messageTrue

/-- Honesty is a lawful predicate on full behavioral classes. -/
def honestClass : fullObserved.Class → Prop :=
  fullObserved.classify HonestCommunication honest_saturated_full

/-- Truth is already lawful on the coarser outcome classes. -/
def trueOutcomeClass : outcomeObserved.Class → Prop :=
  outcomeObserved.classify TrueCommunication true_saturated_outcome

@[simp] theorem honestClass_correct (term : Pattern) :
    honestClass (fullObserved.toClass term) ↔ HonestCommunication term :=
  Iff.rfl

@[simp] theorem trueOutcomeClass_correct (term : Pattern) :
    trueOutcomeClass (outcomeObserved.toClass term) ↔
      TrueCommunication term :=
  Iff.rfl

def honestTrueMessage : Pattern :=
  episode communicating yes yes

def dishonestTrueMessage : Pattern :=
  episode communicating no yes

theorem honest_and_dishonest_true_same_outcome :
    outcomeObserved.Bisimilar honestTrueMessage dishonestTrueMessage :=
  ⟨SameOutcome, sameOutcome_is_observed_bisimulation,
    .inr ⟨communicating, yes, no, yes, rfl, rfl⟩⟩

theorem honest_true_message_is_honest :
    HonestCommunication honestTrueMessage :=
  ⟨communicating, yes, rfl⟩

theorem dishonest_true_message_is_not_honest :
    ¬ HonestCommunication dishonestTrueMessage := by
  rw [dishonestTrueMessage, honestCommunication_episode_iff]
  simp [no, yes]

theorem honest_true_message_is_true : TrueCommunication honestTrueMessage :=
  ⟨communicating, yes, rfl⟩

theorem dishonest_true_message_is_true : TrueCommunication dishonestTrueMessage :=
  ⟨communicating, no, rfl⟩

theorem honest_and_dishonest_true_full_distinction :
    ¬ fullObserved.Bisimilar honestTrueMessage dishonestTrueMessage :=
  fullObserved.distinguished_of_observation .beliefTrue
    honest_true_message_is_honest dishonest_true_message_is_not_honest

/-- Honesty is not saturated by outcome bisimilarity. -/
theorem honest_not_saturated_outcome :
    ¬ outcomeObserved.Saturated HonestCommunication := by
  intro saturated
  have honestyEquivalent :=
    saturated honest_and_dishonest_true_same_outcome
  exact dishonest_true_message_is_not_honest
    (honestyEquivalent.mp honest_true_message_is_honest)

/-- Consequently no predicate on outcome classes can recover honesty for all
communication terms. -/
theorem no_honesty_classifier_on_outcome_classes :
    ¬ ∃ classifier : outcomeObserved.Class → Prop,
      ∀ term, classifier (outcomeObserved.toClass term) ↔
        HonestCommunication term := by
  rintro ⟨classifier, correct⟩
  exact honest_not_saturated_outcome
    (outcomeObserved.saturated_of_classifier
      HonestCommunication classifier correct)

/-! ## Axiom audit -/

#print axioms sameOutcome_is_observed_bisimulation
#print axioms honest_saturated_full
#print axioms true_saturated_outcome
#print axioms honest_and_dishonest_true_same_outcome
#print axioms honest_and_dishonest_true_full_distinction
#print axioms honest_not_saturated_outcome
#print axioms no_honesty_classifier_on_outcome_classes

end Mettapedia.Ethics.EthicalCommunicationBisimulation
