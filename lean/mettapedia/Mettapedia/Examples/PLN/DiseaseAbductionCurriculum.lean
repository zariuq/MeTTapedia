import Mathlib.Tactic
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNAlgorithmicAbductionBridge

/-!
# Disease abduction curriculum example

This file gives a small diagnostic-abduction example over the existing
algorithmic-prior abduction bridge.  A symptom score is just the imported
`priorWeightedPoint`: hypothesis prior times symptom likelihood.
-/

namespace Mettapedia.Examples.PLN.DiseaseAbductionCurriculum

open Mettapedia.PLN.RuleFamilies.FirstOrder

noncomputable section

/-- Minimal finite diagnostic hypothesis used by the worked example. -/
structure DiseaseHypothesis where
  prior : ℝ
  symptomLikelihood : ℝ

/-- Abductive point score for a single symptom. -/
noncomputable def symptomScore (h : DiseaseHypothesis) : ℝ :=
  priorWeightedPoint h.prior h.symptomLikelihood

/-! ## Positive case: a specific symptom can overcome a smaller prior -/

def rareSpecificDisease : DiseaseHypothesis where
  prior := 1 / 100
  symptomLikelihood := 99 / 100

def commonBackgroundCause : DiseaseHypothesis where
  prior := 1 / 5
  symptomLikelihood := 1 / 100

/-- Imported unit-interval preservation applies to the rare-disease score. -/
theorem rare_specific_score_in_unit :
    symptomScore rareSpecificDisease ∈ Set.Icc (0 : ℝ) 1 := by
  unfold symptomScore rareSpecificDisease
  exact priorWeightedPoint_mem_unit_of_mem_unit (by norm_num) (by norm_num)

/-- A discriminating symptom ranks the rarer disease above the broad
background cause. -/
theorem rare_specific_disease_beats_common_background :
    symptomScore commonBackgroundCause < symptomScore rareSpecificDisease := by
  norm_num [symptomScore, commonBackgroundCause, rareSpecificDisease,
    priorWeightedPoint]

/-! ## Negative case: base rate can defeat a noisy positive symptom -/

def rareNoisyDisease : DiseaseHypothesis where
  prior := 1 / 1000
  symptomLikelihood := 99 / 100

def commonNoisyCause : DiseaseHypothesis where
  prior := 1 / 2
  symptomLikelihood := 1 / 100

/-- A high-sensitivity symptom is not automatically a good explanation when
the prior is tiny and the comparison cause is common. -/
theorem noisy_symptom_base_rate_counterexample :
    symptomScore rareNoisyDisease < symptomScore commonNoisyCause := by
  norm_num [symptomScore, rareNoisyDisease, commonNoisyCause,
    priorWeightedPoint]

/-! ## Interval ranking discipline -/

/-- A narrow strong interval for the specific disease. -/
def specificDiseaseInterval :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV where
  lower := 9 / 10
  upper := 1
  credibility := 4 / 5
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- A weak interval for the broad background cause. -/
def backgroundCauseInterval :
    Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV where
  lower := 0
  upper := 1 / 5
  credibility := 1 / 2
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- Positive interval example: separated prior-weighted intervals justify a
strict explanation ranking. -/
theorem specific_interval_strictly_ranks_background :
    priorWeightedIntervalStrictlyRanks
      (1 : ℝ) (1 : ℝ) specificDiseaseInterval backgroundCauseInterval := by
  norm_num [priorWeightedIntervalStrictlyRanks, priorWeightedLower,
    priorWeightedUpper, specificDiseaseInterval, backgroundCauseInterval]

/-- Negative interval example: the imported abduction-search canary has a point
score flip, but its prior-weighted intervals still overlap, so neither interval
robustly outranks the other. -/
theorem overlapping_intervals_block_strict_ranking :
    priorWeightedIntervalsOverlap
      (descriptionLengthPrior 1) (descriptionLengthPrior 2)
      abductionSearchOpenITV abductionSearchBetterPointITV ∧
    ¬ priorWeightedIntervalStrictlyRanks
      (descriptionLengthPrior 1) (descriptionLengthPrior 2)
      abductionSearchOpenITV abductionSearchBetterPointITV ∧
    ¬ priorWeightedIntervalStrictlyRanks
      (descriptionLengthPrior 2) (descriptionLengthPrior 1)
      abductionSearchBetterPointITV abductionSearchOpenITV := by
  rcases algorithmicPriorAbduction_point_flip_not_interval_rank_canary with
    ⟨_, _, _, _, _, _, hOverlap, hOpenNoRank, hBetterNoRank⟩
  exact ⟨hOverlap, hOpenNoRank, hBetterNoRank⟩

end

end Mettapedia.Examples.PLN.DiseaseAbductionCurriculum
