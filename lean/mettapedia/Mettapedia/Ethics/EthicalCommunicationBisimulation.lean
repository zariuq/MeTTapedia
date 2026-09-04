import Mettapedia.Ethics.MetaEthicsOntology
import Mettapedia.GSLT.Core.ObservedBisimulation

/-!
# Honest and true communication as observer-relative behavioral concepts

The Formal Ethics Ontology distinguishes:

* honest communication: the communicator believes the message to be true
  during the communication; and
* true communication: the message is in fact true during the communication.

This module gives that distinction a small operational semantics. Belief and
truth are stable facts of one communication episode while its phase advances.
The full observer can inspect both; the outcome observer can inspect truth and
completion but not belief.

The positive results show that both concepts are saturated unions of classes
for a sufficiently discriminating observer. The negative result shows that
honesty is not a concept on the outcome-only quotient: an honest true message
and a dishonest true message are outcome-bisimilar. This is a precise boundary
on the claim that behavioral equivalence classes form a basis for ontology.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalCommunicationBisimulation

open Mettapedia.GSLT

/-! ## Communication dynamics -/

inductive CommunicationPhase : Type
  | prepared
  | communicating
  | completed
  deriving DecidableEq, Repr

/-- The ethically relevant state of one communication episode. -/
structure CommunicationState : Type where
  phase : CommunicationPhase
  communicatorBelievesTrue : Bool
  messageTrue : Bool
  deriving DecidableEq, Repr

/-- A communication starts and finishes without changing its belief or truth
facts. -/
inductive CommunicationStep : CommunicationState → CommunicationState → Prop
  | start (belief truth : Bool) :
      CommunicationStep
        ⟨.prepared, belief, truth⟩
        ⟨.communicating, belief, truth⟩
  | finish (belief truth : Bool) :
      CommunicationStep
        ⟨.communicating, belief, truth⟩
        ⟨.completed, belief, truth⟩

/-- The communication episode as a GSLT. -/
def communicationGSLT : GSLT where
  Term := CommunicationState
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := CommunicationStep
  rewrites_resp_left := by
    intro left equalLeft right equal step
    subst equalLeft
    exact ⟨right, step, rfl⟩
  rewrites_resp_right := by
    intro left right equalRight step equal
    subst equalRight
    exact step

/-! ## Source concepts -/

/-- The communicator believes the message to be true throughout the episode. -/
def HonestCommunication (state : CommunicationState) : Prop :=
  state.communicatorBelievesTrue = true

/-- The message is true throughout the episode. -/
def TrueCommunication (state : CommunicationState) : Prop :=
  state.messageTrue = true

/-! ## Full and outcome observers -/

inductive FullAtom : Type
  | beliefTrue
  | messageTrue
  | completed
  deriving DecidableEq, Repr

def fullObserved : ObservedGSLT communicationGSLT where
  Atom := FullAtom
  observes atom state :=
    match atom with
    | .beliefTrue => HonestCommunication state
    | .messageTrue => TrueCommunication state
    | .completed => state.phase = .completed

inductive OutcomeAtom : Type
  | messageTrue
  | completed
  deriving DecidableEq, Repr

def outcomeObserved : ObservedGSLT communicationGSLT where
  Atom := OutcomeAtom
  observes atom state :=
    match atom with
    | .messageTrue => TrueCommunication state
    | .completed => state.phase = .completed

/-! ## The outcome bisimulation -/

/-- The outcome observer retains phase and message truth but forgets the
communicator's belief. -/
def SameOutcome (left right : CommunicationState) : Prop :=
  left.phase = right.phase ∧ left.messageTrue = right.messageTrue

theorem SameOutcome.symm {left right : CommunicationState}
    (same : SameOutcome left right) : SameOutcome right left :=
  ⟨same.1.symm, same.2.symm⟩

theorem sameOutcome_forward {left right next : CommunicationState}
    (same : SameOutcome left right)
    (step : communicationGSLT.Step left next) :
    ∃ rightNext, communicationGSLT.Step right rightNext ∧
      SameOutcome next rightNext := by
  cases step with
  | start belief truth =>
      rcases right with ⟨phase, rightBelief, rightTruth⟩
      rcases same with ⟨phaseEqual, truthEqual⟩
      change CommunicationPhase.prepared = phase at phaseEqual
      change truth = rightTruth at truthEqual
      cases phaseEqual
      cases truthEqual
      exact ⟨⟨.communicating, rightBelief, truth⟩,
        .start rightBelief truth, rfl, rfl⟩
  | finish belief truth =>
      rcases right with ⟨phase, rightBelief, rightTruth⟩
      rcases same with ⟨phaseEqual, truthEqual⟩
      change CommunicationPhase.communicating = phase at phaseEqual
      change truth = rightTruth at truthEqual
      cases phaseEqual
      cases truthEqual
      exact ⟨⟨.completed, rightBelief, truth⟩,
        .finish rightBelief truth, rfl, rfl⟩

theorem sameOutcome_is_step_bisimulation :
    communicationGSLT.IsBisimulation SameOutcome := by
  constructor
  · intro left right same next step
    exact sameOutcome_forward same step
  · intro left right same next step
    rcases sameOutcome_forward same.symm step with
      ⟨leftNext, leftStep, nextSame⟩
    exact ⟨leftNext, leftStep, nextSame.symm⟩

theorem sameOutcome_preserves_outcome_atoms
    {left right : CommunicationState} (same : SameOutcome left right)
    (atom : OutcomeAtom) :
    outcomeObserved.observes atom left ↔
      outcomeObserved.observes atom right := by
  rcases same with ⟨phaseEqual, truthEqual⟩
  cases atom
  · change (left.messageTrue = true ↔ right.messageTrue = true)
    rw [truthEqual]
  · change (left.phase = .completed ↔ right.phase = .completed)
    rw [phaseEqual]

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

@[simp] theorem honestClass_correct (state : CommunicationState) :
    honestClass (fullObserved.toClass state) ↔ HonestCommunication state :=
  Iff.rfl

@[simp] theorem trueOutcomeClass_correct (state : CommunicationState) :
    trueOutcomeClass (outcomeObserved.toClass state) ↔
      TrueCommunication state :=
  Iff.rfl

def honestTrueMessage : CommunicationState :=
  ⟨.communicating, true, true⟩

def dishonestTrueMessage : CommunicationState :=
  ⟨.communicating, false, true⟩

theorem honest_and_dishonest_true_same_outcome :
    outcomeObserved.Bisimilar honestTrueMessage dishonestTrueMessage :=
  ⟨SameOutcome, sameOutcome_is_observed_bisimulation, by
    exact ⟨rfl, rfl⟩⟩

theorem honest_and_dishonest_true_full_distinction :
    ¬ fullObserved.Bisimilar honestTrueMessage dishonestTrueMessage :=
  fullObserved.distinguished_of_observation .beliefTrue
    (by rfl) (by simp [fullObserved, HonestCommunication,
      dishonestTrueMessage])

theorem honest_true_message_is_honest :
    HonestCommunication honestTrueMessage :=
  rfl

theorem dishonest_true_message_is_not_honest :
    ¬ HonestCommunication dishonestTrueMessage := by
  simp [HonestCommunication, dishonestTrueMessage]

/-- Honesty is not saturated by outcome bisimilarity. -/
theorem honest_not_saturated_outcome :
    ¬ outcomeObserved.Saturated HonestCommunication := by
  intro saturated
  have honestyEquivalent :=
    saturated honest_and_dishonest_true_same_outcome
  exact dishonest_true_message_is_not_honest
    (honestyEquivalent.mp honest_true_message_is_honest)

/-- Consequently no predicate on outcome classes can recover honesty for all
communication states. -/
theorem no_honesty_classifier_on_outcome_classes :
    ¬ ∃ classifier : outcomeObserved.Class → Prop,
      ∀ state, classifier (outcomeObserved.toClass state) ↔
        HonestCommunication state := by
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
