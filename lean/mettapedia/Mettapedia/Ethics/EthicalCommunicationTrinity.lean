import Mettapedia.Ethics.EthicalCommunicationConceptFormation
import Mettapedia.TypeTheory.DisplayedEvidence

/-!
# One ethical communication through operational, dependent, and extensional faces

This module carries the same Formal Ethics communication specimen through
three semantic faces:

* the operational face is the communication GSLT and its concrete rewrite
  paths;
* the dependent face displays honesty evidence over the exact communication
  state and retains whether the communicator believes the message;
* the extensional face quotients by the outcome observer, retaining message
  truth and completion while forgetting belief.

The induced map from belief-sensitive behavioral classes to outcome classes
is surjective and the triangle from raw states commutes.  It is not injective:
honest and dishonest true communications have the same outcome class.
Accordingly, truth evidence descends to outcome classes while honesty evidence
does not.

This is an observer boundary, not a claim that extensional set theory cannot
encode beliefs.  An extensional host can retain the full state by choosing a
finer object.  The theorem says that the declared outcome quotient cannot
recover information it deliberately erased.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalCommunicationTrinity

open Mettapedia.GSLT
open Mettapedia.GSLT.ObservedGSLT
open Mettapedia.TypeTheory.DisplayedEvidence
open EthicalCommunicationBisimulation
open EthicalCommunicationConceptFormation

/-! ## Operational paths -/

abbrev honestPrepared : CommunicationState :=
  ⟨.prepared, true, true⟩

abbrev honestCompleted : CommunicationState :=
  ⟨.completed, true, true⟩

abbrev dishonestPrepared : CommunicationState :=
  ⟨.prepared, false, true⟩

abbrev dishonestCompleted : CommunicationState :=
  ⟨.completed, false, true⟩

def honestStartStep :
    communicationGSLT.Step honestPrepared honestTrueMessage := by
  change CommunicationStep honestPrepared honestTrueMessage
  simpa [honestTrueMessage] using CommunicationStep.start true true

def honestFinishStep :
    communicationGSLT.Step honestTrueMessage honestCompleted := by
  change CommunicationStep honestTrueMessage honestCompleted
  simpa [honestTrueMessage] using CommunicationStep.finish true true

def dishonestStartStep :
    communicationGSLT.Step dishonestPrepared dishonestTrueMessage := by
  change CommunicationStep dishonestPrepared dishonestTrueMessage
  simpa [dishonestTrueMessage] using CommunicationStep.start false true

def dishonestFinishStep :
    communicationGSLT.Step dishonestTrueMessage dishonestCompleted := by
  change CommunicationStep dishonestTrueMessage dishonestCompleted
  simpa [dishonestTrueMessage] using CommunicationStep.finish false true

/-- The honest route contains both authored communication transitions. -/
def honestRoute : communicationGSLT.RewritePath honestPrepared honestCompleted :=
  .cons honestStartStep (.cons honestFinishStep
    (GSLT.RewritePath.nil (S := communicationGSLT) honestCompleted))

/-- A visibly identical truth/completion route with different belief state. -/
def dishonestRoute :
  communicationGSLT.RewritePath dishonestPrepared dishonestCompleted :=
  .cons dishonestStartStep
    (.cons dishonestFinishStep
      (GSLT.RewritePath.nil (S := communicationGSLT) dishonestCompleted))

@[simp] theorem honestRoute_length : honestRoute.length = 2 := rfl

@[simp] theorem dishonestRoute_length : dishonestRoute.length = 2 := rfl

/-! ## Dependent evidence over exact states -/

/-- Honesty is an exact evidence family indexed by the operational state. -/
def honestyFamily : Family where
  Raw := CommunicationState
  Exact := fun state => PLift (HonestCommunication state)

def honestTrueStatus : Status honestyFamily Unit honestTrueMessage :=
  .established ⟨honest_true_message_is_honest⟩

def dishonestTrueRefutation :
    Refutation honestyFamily Unit dishonestTrueMessage where
  reason := ()
  refutes := fun evidence =>
    dishonest_true_message_is_not_honest evidence.down

def dishonestTrueStatus : Status honestyFamily Unit dishonestTrueMessage :=
  .refuted dishonestTrueRefutation

/-- An honest receipt retains the exact state on which its evidence depends. -/
abbrev HonestReceipt := Sigma honestyFamily.Exact

def honestTrueReceipt : HonestReceipt :=
  ⟨honestTrueMessage, ⟨honest_true_message_is_honest⟩⟩

/-! ## Forgetting belief -/

/-- Every full-observer bisimulation is also an outcome-observer
bisimulation because every outcome atom is among the full atoms. -/
theorem fullBisimilar_implies_outcomeBisimilar
    {left right : CommunicationState}
    (bisimilar : fullObserved.Bisimilar left right) :
    outcomeObserved.Bisimilar left right := by
  rcases bisimilar with ⟨relation, ⟨stepBisimulation, observations⟩, related⟩
  refine ⟨relation, ⟨stepBisimulation, ?_⟩, related⟩
  intro first second relatedStates atom
  cases atom with
  | messageTrue => exact observations relatedStates .messageTrue
  | completed => exact observations relatedStates .completed

/-- The extensional readout from belief-sensitive behavioral classes to
outcome behavioral classes. -/
def forgetBelief : fullObserved.Class → outcomeObserved.Class :=
  Quotient.map id fun _left _right bisimilar =>
    fullBisimilar_implies_outcomeBisimilar bisimilar

@[simp] theorem forgetBelief_toClass (state : CommunicationState) :
    forgetBelief (fullObserved.toClass state) =
      outcomeObserved.toClass state :=
  rfl

/-- Raw-state observation commutes through the belief-sensitive face. -/
theorem observation_triangle_commutes (state : CommunicationState) :
    forgetBelief (fullObserved.toClass state) =
      outcomeObserved.toClass state :=
  rfl

/-- Every outcome class has a belief-sensitive representative. -/
theorem forgetBelief_surjective : Function.Surjective forgetBelief := by
  intro outcomeClass
  refine Quotient.inductionOn outcomeClass ?_
  intro state
  exact ⟨fullObserved.toClass state, rfl⟩

theorem honest_and_dishonest_true_same_extensional_class :
    forgetBelief (fullObserved.toClass honestTrueMessage) =
      forgetBelief (fullObserved.toClass dishonestTrueMessage) := by
  change outcomeObserved.toClass honestTrueMessage =
    outcomeObserved.toClass dishonestTrueMessage
  exact (outcomeObserved.class_eq_iff _ _).2
    honest_and_dishonest_true_same_outcome

/-- The extensional readout is genuinely nonfaithful. -/
theorem forgetBelief_not_injective : ¬ Function.Injective forgetBelief := by
  intro injective
  have equalFullClasses := injective
    honest_and_dishonest_true_same_extensional_class
  exact honest_and_dishonest_true_full_distinction
    ((fullObserved.class_eq_iff _ _).1 equalFullClasses)

/-! ## Exact descent boundary -/

/-- Truth evidence is a family on the outcome quotient itself. -/
def OutcomeTruthEvidence (outcomeClass : outcomeObserved.Class) : Type :=
  PLift (trueOutcomeClass outcomeClass)

theorem truthEvidence_descends (state : CommunicationState) :
    TrueCommunication state ↔
      Nonempty (OutcomeTruthEvidence (outcomeObserved.toClass state)) := by
  constructor
  · intro truth
    exact ⟨⟨truth⟩⟩
  · rintro ⟨truth⟩
    exact truth.down

/-- No type family over outcome classes can be fibrewise equivalent to exact
honesty evidence at every operational state. -/
theorem honestyEvidence_does_not_descend :
    ¬ ∃ family : outcomeObserved.Class → Type,
      ∀ state : CommunicationState,
        Nonempty (PLift (HonestCommunication state) ≃
          family (outcomeObserved.toClass state)) := by
  rintro ⟨family, descends⟩
  obtain ⟨honestEquiv⟩ := descends honestTrueMessage
  obtain ⟨dishonestEquiv⟩ := descends dishonestTrueMessage
  let evidenceAtHonestClass : family (outcomeObserved.toClass honestTrueMessage) :=
    honestEquiv ⟨honest_true_message_is_honest⟩
  have sameClass : outcomeObserved.toClass honestTrueMessage =
      outcomeObserved.toClass dishonestTrueMessage :=
    (outcomeObserved.class_eq_iff _ _).2
      honest_and_dishonest_true_same_outcome
  have evidenceAtDishonestClass :
      family (outcomeObserved.toClass dishonestTrueMessage) := by
    rw [← sameClass]
    exact evidenceAtHonestClass
  exact dishonest_true_message_is_not_honest
    (dishonestEquiv.symm evidenceAtDishonestClass).down

/-- The FCA negative and the dependent-family negative express the same
observer failure at proposition-valued and type-valued levels. -/
theorem outcome_forgets_honesty_at_both_levels :
    (¬ ∃ property : outcomeObserved.BehavioralAttribute,
        property.holds = HonestCommunication) ∧
      (¬ ∃ family : outcomeObserved.Class → Type,
        ∀ state : CommunicationState,
          Nonempty (PLift (HonestCommunication state) ≃
            family (outcomeObserved.toClass state))) :=
  ⟨no_outcome_honesty_attribute, honestyEvidence_does_not_descend⟩

/-! ## Axiom audit -/

#print axioms fullBisimilar_implies_outcomeBisimilar
#print axioms observation_triangle_commutes
#print axioms forgetBelief_surjective
#print axioms forgetBelief_not_injective
#print axioms truthEvidence_descends
#print axioms honestyEvidence_does_not_descend
#print axioms outcome_forgets_honesty_at_both_levels

end Mettapedia.Ethics.EthicalCommunicationTrinity
