import Mettapedia.Ethics.EthicalCommunicationBisimulation
import Mettapedia.GSLT.Core.ObservedConceptFormation

/-!
# Formal concepts for honest and true communication

The operational communication example now supplies objects and attributes to
formal concept analysis.  Under the full observer, honesty and truth define
behavioral attributes and therefore extents of behavioral classes.  Under the
outcome observer, truth still does, while honesty cannot: honest and dishonest
true messages inhabit the same outcome class.

This is both a positive specimen of behaviorally grounded concept formation
and a negative check on observer choice.  Coarsening the observer may destroy
an ethically relevant concept even when the visible outcome is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalCommunicationConceptFormation

open Mettapedia.GSLT
open Mettapedia.GSLT.ObservedGSLT
open EthicalCommunicationBisimulation

/-- Honesty as a saturated attribute for the full communication observer. -/
def fullHonestyAttribute : fullObserved.BehavioralAttribute where
  holds := HonestCommunication
  saturated := honest_saturated_full

/-- Truth as a saturated attribute for the full communication observer. -/
def fullTruthAttribute : fullObserved.BehavioralAttribute where
  holds := TrueCommunication
  saturated := true_saturated_full

/-- Truth as a saturated attribute for the outcome-only observer. -/
def outcomeTruthAttribute : outcomeObserved.BehavioralAttribute where
  holds := TrueCommunication
  saturated := true_saturated_outcome

theorem honest_true_message_in_full_honesty_extent :
    fullObserved.toClass honestTrueMessage ∈
      fullObserved.behavioralExtent fullHonestyAttribute := by
  simp [fullHonestyAttribute, honest_true_message_is_honest]

theorem dishonest_true_message_not_in_full_honesty_extent :
    fullObserved.toClass dishonestTrueMessage ∉
      fullObserved.behavioralExtent fullHonestyAttribute := by
  simp [fullHonestyAttribute, dishonest_true_message_is_not_honest]

/-- The honesty attribute separates the two full behavioral classes. -/
theorem honesty_separates_full_classes :
    fullObserved.toClass honestTrueMessage ≠
      fullObserved.toClass dishonestTrueMessage :=
  fullObserved.class_ne_of_attribute_disagreement fullHonestyAttribute
    honest_true_message_is_honest dishonest_true_message_is_not_honest

theorem honest_true_message_in_full_truth_extent :
    fullObserved.toClass honestTrueMessage ∈
      fullObserved.behavioralExtent fullTruthAttribute := by
  simp [fullTruthAttribute, TrueCommunication, honestTrueMessage]

theorem honest_true_message_in_outcome_truth_extent :
    outcomeObserved.toClass honestTrueMessage ∈
      outcomeObserved.behavioralExtent outcomeTruthAttribute := by
  simp [outcomeTruthAttribute, TrueCommunication, honestTrueMessage]

theorem dishonest_true_message_in_outcome_truth_extent :
    outcomeObserved.toClass dishonestTrueMessage ∈
      outcomeObserved.behavioralExtent outcomeTruthAttribute := by
  simp [outcomeTruthAttribute, TrueCommunication, dishonestTrueMessage]

/-- There is no outcome-observer behavioral attribute whose state predicate
is honesty.  The missing concept cannot be repaired by merely renaming an
outcome attribute. -/
theorem no_outcome_honesty_attribute :
    ¬ ∃ property : outcomeObserved.BehavioralAttribute,
      property.holds = HonestCommunication := by
  rintro ⟨property, holdsEqual⟩
  apply honest_not_saturated_outcome
  rw [← holdsEqual]
  exact property.saturated

/-! ## Axiom audit -/

#print axioms honest_true_message_in_full_honesty_extent
#print axioms dishonest_true_message_not_in_full_honesty_extent
#print axioms honesty_separates_full_classes
#print axioms honest_true_message_in_outcome_truth_extent
#print axioms no_outcome_honesty_attribute

end Mettapedia.Ethics.EthicalCommunicationConceptFormation
