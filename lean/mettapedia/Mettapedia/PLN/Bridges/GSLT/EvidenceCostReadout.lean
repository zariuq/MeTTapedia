import Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
import Mettapedia.PLN.Bridges.GSLT.InferenceControl
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

/-!
# PLN evidence readouts and cost-sensitive choice

Full PLN evidence, its scalar scheduler readout, and predicted resource cost
serve different purposes:

* `BinaryEvidence` is the revisable epistemic state;
* `propensity = strength * confidence` is a declared scalar readout;
* estimated cost is an independent policy input, not evidence and not an
  execution receipt.

This file proves three boundaries needed by graded inference control.  The
propensity readout is not injective and cannot be revised without the retained
evidence.  Confidence cancels from a race between complementary branches, but
becomes observable against an independently weighted alternative.  Finally, a
cost-sensitive policy may combine propensity and predicted cost while the
existing `Guidance` carrier retains both inputs separately.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout

open scoped ENNReal

open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Bridges.GSLT.InferenceControl
open Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.InferenceControl.PremiseSelection
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

noncomputable section

/-! ## A scalar propensity is not a revisable evidence state -/

/-- One positive observation and no negative observations. -/
def concentratedEvidence : BinaryEvidence := ⟨1, 0⟩

/-- Two positive observations and one negative observation. -/
def mixedEvidence : BinaryEvidence := ⟨2, 1⟩

/-- One additional positive observation, used to test future revision. -/
def positiveObservation : BinaryEvidence := ⟨1, 0⟩

/-- Distinct PLN states can have the same strength-times-confidence readout.
With unit prior, both examples have propensity `1 / 2`. -/
theorem propensity_collision :
    propensity 1 concentratedEvidence = propensity 1 mixedEvidence := by
  have concentratedFinite : propensity 1 concentratedEvidence ≠ ⊤ := by
    change (1 : ℝ≥0∞) / (1 + 0 + 1) ≠ ⊤
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have mixedFinite : propensity 1 mixedEvidence ≠ ⊤ := by
    change (2 : ℝ≥0∞) / (2 + 1 + 1) ≠ ⊤
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  apply (ENNReal.toReal_eq_toReal_iff' concentratedFinite mixedFinite).mp
  norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
    BinaryEvidence.total, concentratedEvidence, mixedEvidence,
    ENNReal.toReal_div]

/-- The colliding propensity values come from genuinely different evidence. -/
theorem concentratedEvidence_ne_mixedEvidence :
    concentratedEvidence ≠ mixedEvidence := by
  intro equal
  have negativeEqual := congrArg BinaryEvidence.neg equal
  norm_num [concentratedEvidence, mixedEvidence] at negativeEqual

/-- The same new observation separates the two states that the scalar readout
identified.  Revision must therefore happen on full evidence before readout. -/
theorem revised_propensity_separates_collision :
    propensity 1 (revision concentratedEvidence positiveObservation) ≠
      propensity 1 (revision mixedEvidence positiveObservation) := by
  intro equal
  have realEqual := congrArg ENNReal.toReal equal
  norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
    BinaryEvidence.total, revision, BinaryEvidence.hplus_def,
    concentratedEvidence, mixedEvidence, positiveObservation,
    ENNReal.toReal_div] at realEqual

/-- No function of the scalar propensity alone can reconstruct both colliding
evidence states.  This is the exact information-loss theorem for this readout,
not a claim about arbitrary encodings of pairs. -/
theorem no_evidence_reconstruction_from_propensity :
    ¬ ∃ recover : ℝ≥0∞ → BinaryEvidence,
        recover (propensity 1 concentratedEvidence) = concentratedEvidence ∧
        recover (propensity 1 mixedEvidence) = mixedEvidence := by
  rintro ⟨recover, concentratedRecovered, mixedRecovered⟩
  have recoveredEqual := congrArg recover propensity_collision
  apply concentratedEvidence_ne_mixedEvidence
  exact concentratedRecovered.symm.trans (recoveredEqual.trans mixedRecovered)

/-! ## Confidence cancellation and visibility -/

/-- Normalized probability that the left branch wins a two-way race. -/
def normalizedRace (left right : ℝ) : ℝ :=
  left / (left + right)

/-- A confirming branch has weight `strength * confidence`; its complementary
branch has weight `(1 - strength) * confidence`. -/
def complementaryRace (strength confidence : ℝ) : ℝ :=
  normalizedRace (strength * confidence) ((1 - strength) * confidence)

/-- Confidence cancels exactly when both alternatives share the same nonzero
confidence factor. -/
theorem complementaryRace_eq_strength
    (strength confidence : ℝ) (confidence_ne_zero : confidence ≠ 0) :
    complementaryRace strength confidence = strength := by
  unfold complementaryRace normalizedRace
  have denominator :
      strength * confidence + (1 - strength) * confidence = confidence := by
    ring
  rw [denominator]
  exact mul_div_cancel_right₀ strength confidence_ne_zero

/-- Race against an independently weighted outside option. -/
def outsideOptionRace (strength confidence outsideWeight : ℝ) : ℝ :=
  normalizedRace (strength * confidence) outsideWeight

/-- Against a positive independent outside option, increasing confidence
strictly increases the probability of choosing a positive-strength action. -/
theorem outsideOptionRace_strictMono_confidence
    {strength outsideWeight lowConfidence highConfidence : ℝ}
    (strength_pos : 0 < strength)
    (outside_pos : 0 < outsideWeight)
    (low_nonnegative : 0 ≤ lowConfidence)
    (confidence_lt : lowConfidence < highConfidence) :
    outsideOptionRace strength lowConfidence outsideWeight <
      outsideOptionRace strength highConfidence outsideWeight := by
  unfold outsideOptionRace normalizedRace
  have lowDenominatorPos :
      0 < strength * lowConfidence + outsideWeight := by
    have productNonnegative := mul_nonneg (le_of_lt strength_pos) low_nonnegative
    linarith
  have highNonnegative : 0 ≤ highConfidence := le_trans low_nonnegative
    (le_of_lt confidence_lt)
  have highDenominatorPos :
      0 < strength * highConfidence + outsideWeight := by
    have productNonnegative := mul_nonneg (le_of_lt strength_pos) highNonnegative
    linarith
  rw [div_lt_div_iff₀ lowDenominatorPos highDenominatorPos]
  have scaledConfidence :
      strength * outsideWeight * lowConfidence <
        strength * outsideWeight * highConfidence :=
    mul_lt_mul_of_pos_left confidence_lt (mul_pos strength_pos outside_pos)
  nlinarith

/-! ## Cost makes confidence decision-relevant -/

/-- A simple declared decision boundary: act when confidence-weighted expected
benefit exceeds an independently accounted cost. -/
def costAccepts
    (benefit cost strength confidence : ℝ) : Prop :=
  cost < benefit * strength * confidence

/-- Any strict confidence difference can be exposed by some cost threshold
when benefit and strength are positive.  Cost is therefore an independent
coordinate capable of making confidence behaviorally observable. -/
theorem exists_cost_separating_confidences
    {benefit strength lowConfidence highConfidence : ℝ}
    (benefit_pos : 0 < benefit)
    (strength_pos : 0 < strength)
    (confidence_lt : lowConfidence < highConfidence) :
    ∃ cost,
      ¬ costAccepts benefit cost strength lowConfidence ∧
        costAccepts benefit cost strength highConfidence := by
  let lowValue := benefit * strength * lowConfidence
  let highValue := benefit * strength * highConfidence
  have value_lt : lowValue < highValue := by
    exact mul_lt_mul_of_pos_left confidence_lt
      (mul_pos benefit_pos strength_pos)
  refine ⟨(lowValue + highValue) / 2, ?_, ?_⟩
  · unfold costAccepts
    dsimp [lowValue, highValue]
    linarith
  · unfold costAccepts
    dsimp [lowValue, highValue]
    linarith

/-! ## One explicit cost-aware policy readout -/

/-- A declared, non-canonical policy readout that discounts PLN propensity by
one plus predicted cost.  The surrounding `Guidance` value still retains the
full evidence and the raw estimate independently. -/
def inverseCostPriority
    (prior : ℝ≥0∞) (evidence : BinaryEvidence) (predictedCost : ℝ≥0∞) : ℝ≥0∞ :=
  propensity prior evidence / (predictedCost + 1)

/-- Build an occurrence-preserving guidance policy using the explicit inverse-
cost readout.  This chooses an ordering policy; it does not authorize edges or
state the cost actually incurred. -/
def inverseCostGuidance
    {Goal Node : Type*}
    (prior : ℝ≥0∞) (scorer : Scorer Goal Node)
    (estimate : Goal → Node → ℝ≥0∞) :
    Guidance Goal Node ℝ≥0∞ ℝ≥0∞ where
  scorer := scorer
  estimate := estimate
  rank := inverseCostPriority prior
  prefer := fun first second => second ≤ first

@[simp] theorem inverseCostGuidance_evidenceAt
    {Goal Node : Type*}
    (prior : ℝ≥0∞) (scorer : Scorer Goal Node)
    (estimate : Goal → Node → ℝ≥0∞) (goal : Goal) (node : Node) :
    (inverseCostGuidance prior scorer estimate).evidenceAt goal node =
      scorer.score goal node :=
  rfl

@[simp] theorem inverseCostGuidance_estimateAt
    {Goal Node : Type*}
    (prior : ℝ≥0∞) (scorer : Scorer Goal Node)
    (estimate : Goal → Node → ℝ≥0∞) (goal : Goal) (node : Node) :
    (inverseCostGuidance prior scorer estimate).estimateAt goal node =
      estimate goal node :=
  rfl

@[simp] theorem inverseCostGuidance_priorityAt
    {Goal Node : Type*}
    (prior : ℝ≥0∞) (scorer : Scorer Goal Node)
    (estimate : Goal → Node → ℝ≥0∞) (goal : Goal) (node : Node) :
    (inverseCostGuidance prior scorer estimate).priorityAt goal node =
      inverseCostPriority prior (scorer.score goal node) (estimate goal node) :=
  rfl

/-- Applying the same cost adjustment after the lossy scalar projection does
not restore the evidence information that propensity discarded. -/
theorem inverseCostPriority_collision (predictedCost : ℝ≥0∞) :
    inverseCostPriority 1 concentratedEvidence predictedCost =
      inverseCostPriority 1 mixedEvidence predictedCost := by
  unfold inverseCostPriority
  rw [propensity_collision]

/-- Predicted cost genuinely affects the declared policy readout. -/
theorem inverseCostPriority_distinguishes_cost :
    inverseCostPriority 1 concentratedEvidence 0 ≠
      inverseCostPriority 1 concentratedEvidence 1 := by
  intro equal
  have realEqual := congrArg ENNReal.toReal equal
  norm_num [inverseCostPriority, propensity,
    ScoreFusion.binaryEvidenceFusedQuality, BinaryEvidence.total,
    concentratedEvidence, ENNReal.toReal_div] at realEqual

/-- Retaining full evidence permits revision to separate states even after
the same cost adjustment. -/
theorem revised_inverseCostPriority_separates_collision :
    inverseCostPriority 1
        (revision concentratedEvidence positiveObservation) 0 ≠
      inverseCostPriority 1
        (revision mixedEvidence positiveObservation) 0 := by
  simpa [inverseCostPriority] using revised_propensity_separates_collision

#print axioms propensity_collision
#print axioms revised_propensity_separates_collision
#print axioms no_evidence_reconstruction_from_propensity
#print axioms complementaryRace_eq_strength
#print axioms outsideOptionRace_strictMono_confidence
#print axioms exists_cost_separating_confidences
#print axioms inverseCostPriority_collision
#print axioms inverseCostPriority_distinguishes_cost
#print axioms revised_inverseCostPriority_separates_collision

end

end Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout
