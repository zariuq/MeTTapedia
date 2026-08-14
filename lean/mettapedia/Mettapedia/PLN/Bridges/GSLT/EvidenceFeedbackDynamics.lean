import Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout

/-!
# Support-gated PLN feedback dynamics

A zero propensity is merely a low ordering grade in an occurrence-preserving
controller, but it suppresses a transition in support-gated graded semantics.
This module states that distinction explicitly and proves the resulting
bootstrap fixed point.  It also proves that an authored positive exploration
grade breaks the fixed point.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceFeedbackDynamics

open scoped ENNReal

open Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
open Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

noncomputable section

/-- The support predicate for an authored scalar graded transition. -/
def ScalarSupported (grade : ℝ≥0∞) : Prop :=
  grade ≠ 0

local instance scalarSupportedDecidable (grade : ℝ≥0∞) :
    Decidable (ScalarSupported grade) :=
  Classical.propDecidable _

/-- A minimal support-gated evidence update.  The observation is revised into
the state exactly when the current PLN propensity lies in scalar support. -/
def supportGatedStep
    (prior : ℝ≥0∞) (observation state : BinaryEvidence) : BinaryEvidence :=
  if ScalarSupported (propensity prior state) then revision state observation
  else state

theorem supportGatedStep_eq_self_of_propensity_eq_zero
    (prior : ℝ≥0∞) (observation state : BinaryEvidence)
    (zeroPropensity : propensity prior state = 0) :
    supportGatedStep prior observation state = state := by
  simp [supportGatedStep, ScalarSupported, zeroPropensity]

theorem supportGatedStep_eq_revision_of_propensity_ne_zero
    (prior : ℝ≥0∞) (observation state : BinaryEvidence)
    (nonzeroPropensity : propensity prior state ≠ 0) :
    supportGatedStep prior observation state = revision state observation := by
  simp [supportGatedStep, ScalarSupported, nonzeroPropensity]

/-- No evidence has zero propensity for every prior, including the degenerate
zero prior under `ENNReal` division conventions. -/
theorem zeroEvidence_propensity (prior : ℝ≥0∞) :
    propensity prior (0 : BinaryEvidence) = 0 := by
  simp [propensity, ScoreFusion.binaryEvidenceFusedQuality,
    BinaryEvidence.total]

/-- Bootstrap trap: if observations arrive only after a support-gated action,
the empty evidence state is absorbing. -/
theorem zeroEvidence_is_supportGated_fixedPoint
    (prior : ℝ≥0∞) (observation : BinaryEvidence) :
    supportGatedStep prior observation 0 = 0 := by
  exact supportGatedStep_eq_self_of_propensity_eq_zero prior observation 0
    (zeroEvidence_propensity prior)

/-- Add an authored scalar exploration grade to the PLN propensity. -/
def exploratoryGrade
    (prior exploration : ℝ≥0∞) (state : BinaryEvidence) : ℝ≥0∞ :=
  propensity prior state + exploration

/-- The corresponding support-gated update with explicit exploration. -/
def exploratoryStep
    (prior exploration : ℝ≥0∞)
    (observation state : BinaryEvidence) : BinaryEvidence :=
  if ScalarSupported (exploratoryGrade prior exploration state) then
    revision state observation
  else state

theorem zeroEvidence_exploratoryGrade
    (prior exploration : ℝ≥0∞) :
    exploratoryGrade prior exploration 0 = exploration := by
  simp [exploratoryGrade, zeroEvidence_propensity]

/-- Any positive/nonzero authored exploration grade enables the first update
from empty evidence. -/
theorem exploration_breaks_zeroEvidence_fixedPoint
    (prior exploration : ℝ≥0∞) (observation : BinaryEvidence)
    (exploration_ne_zero : exploration ≠ 0) :
    exploratoryStep prior exploration observation 0 = observation := by
  have supported :
      ScalarSupported (exploratoryGrade prior exploration 0) := by
    simpa [ScalarSupported, zeroEvidence_exploratoryGrade]
  simp [exploratoryStep, supported, revision]

/-- Positive canary: one unit of exploration admits one positive observation
from the empty state. -/
example :
    exploratoryStep 1 1
        Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout.positiveObservation 0 =
      Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout.positiveObservation := by
  exact exploration_breaks_zeroEvidence_fixedPoint 1 1 _ (by norm_num)

/-- Negative canary: without exploration, the same observation cannot enter. -/
example :
    supportGatedStep 1
        Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout.positiveObservation 0 ≠
      Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout.positiveObservation := by
  rw [zeroEvidence_is_supportGated_fixedPoint]
  exact ne_of_apply_ne BinaryEvidence.pos (by norm_num
    [Mettapedia.PLN.Bridges.GSLT.EvidenceCostReadout.positiveObservation])

#print axioms supportGatedStep_eq_self_of_propensity_eq_zero
#print axioms supportGatedStep_eq_revision_of_propensity_ne_zero
#print axioms zeroEvidence_propensity
#print axioms zeroEvidence_is_supportGated_fixedPoint
#print axioms exploration_breaks_zeroEvidence_fixedPoint

end

end Mettapedia.PLN.Bridges.GSLT.EvidenceFeedbackDynamics
