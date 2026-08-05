import Mettapedia.MachineLearning.ContinualLearning.TemporalWeightEnsemble

/-!
# Stochastic semantic memory and temporal-ensemble bridge

The stochastic semantic memories of Arani, Sarfraz, and Zonooz
(arXiv:2201.12604) and the deterministic temporal weight ensemble of
Soutif-Cormerais, Carta, and Van de Weijer (arXiv:2306.16817) share an exact
mean recurrence.

For stochastic update probability `rate` and EMA decay `alpha`, the mean
update is the deterministic EMA whose decay is

`1 - rate * (1 - alpha)`.

This file proves that one-step and finite fixed-target correspondence.  It
also proves the strict mechanism boundary: when the update coin and target
displacement are nondegenerate, stochastic semantic memory has positive
branch variance even though its mean is exactly reproduced by deterministic
EMA.  Mean-trajectory equality is therefore not a mechanism-equivalence
certificate.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SemanticMemoryTemporalBridge

noncomputable section

open StochasticSemanticMemory
open TemporalWeightEnsemble

variable {State : Type*}

section MeanBridge

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Effective deterministic decay corresponding to a stochastic semantic
memory's Bernoulli mean. -/
def effectiveDecay (rate alpha : ℝ) : ℝ :=
  1 - effectiveGain rate alpha

/-- Exact one-step correspondence between the stochastic mean and a
deterministic EMA. -/
theorem bernoulliMean_eq_emaUpdate_effectiveDecay
    (rate alpha : ℝ) (memory target : State) :
    bernoulliMean rate alpha memory target =
      emaUpdate (effectiveDecay rate alpha) memory target := by
  rw [bernoulliMean_eq_interpolation, emaUpdate_eq_interpolation]
  unfold effectiveDecay
  module

/-- A valid stochastic update induces a valid deterministic decay. -/
theorem effectiveDecay_mem_Icc
    (rate alpha : ℝ)
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) :
    effectiveDecay rate alpha ∈ Set.Icc (0 : ℝ) 1 := by
  have gain_bounds := effectiveGain_mem_Icc rate alpha
    rate_nonnegative rate_le_one alpha_nonnegative alpha_le_one
  rcases gain_bounds with ⟨gain_nonnegative, gain_le_one⟩
  constructor <;> unfold effectiveDecay <;> linarith

/-- Chronological iteration of stochastic semantic-memory means against a
possibly moving sequence of working-model targets. -/
def bernoulliMeanRun
    (rate alpha : ℝ) : List State → State → State
  | [], memory => memory
  | target :: targets, memory =>
      bernoulliMeanRun rate alpha targets
        (bernoulliMean rate alpha memory target)

/-- For every chronological target sequence, stochastic semantic memory's
mean trajectory is exactly a deterministic EMA trajectory at the effective
decay. -/
theorem bernoulliMeanRun_eq_emaRun_effectiveDecay
    (rate alpha : ℝ) (targets : List State) (memory : State) :
    bernoulliMeanRun rate alpha targets memory =
      emaRun (effectiveDecay rate alpha) targets memory := by
  induction targets generalizing memory with
  | nil => rfl
  | cons target targets ih =>
      simp only [bernoulliMeanRun, emaRun_cons]
      rw [bernoulliMean_eq_emaUpdate_effectiveDecay]
      exact ih (emaUpdate (effectiveDecay rate alpha) memory target)

/-- Valid stochastic parameters transport the deterministic temporal
ensemble's checkpointwise deviation budget to the full moving-target mean
trajectory. -/
theorem bernoulliMeanRun_norm_sub_le_discounted
    (rate alpha : ℝ) (targets : List State)
    (memory reference : State)
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha)
    (alpha_le_one : alpha ≤ 1) :
    ‖bernoulliMeanRun rate alpha targets memory - reference‖ ≤
      effectiveDecay rate alpha ^ targets.length *
          ‖memory - reference‖ +
        discountedCheckpointDeviation
          (effectiveDecay rate alpha) reference targets := by
  rw [bernoulliMeanRun_eq_emaRun_effectiveDecay]
  have bounds := effectiveDecay_mem_Icc rate alpha
    rate_nonnegative rate_le_one alpha_nonnegative alpha_le_one
  exact emaRun_norm_sub_le_discounted
    (effectiveDecay rate alpha) targets memory reference
    bounds.1 bounds.2

/-- Applying one mean update before or after any number of fixed-target mean
updates gives the same result. -/
theorem meanIterate_bernoulliMean
    (rate alpha : ℝ) (target memory : State) (steps : ℕ) :
    meanIterate rate alpha target steps
        (bernoulliMean rate alpha memory target) =
      bernoulliMean rate alpha
        (meanIterate rate alpha target steps memory) target := by
  apply sub_left_injective (b := target)
  change
    meanIterate rate alpha target steps
          (bernoulliMean rate alpha memory target) - target =
      bernoulliMean rate alpha
          (meanIterate rate alpha target steps memory) target - target
  rw [meanIterate_sub_target, bernoulliMean_sub_target,
    bernoulliMean_sub_target, meanIterate_sub_target, smul_smul, smul_smul]
  congr 1
  ring

/-- Repeating one fixed checkpoint under the effective deterministic decay is
exactly the iterated stochastic mean trajectory. -/
theorem emaRun_replicate_effectiveDecay_eq_meanIterate
    (rate alpha : ℝ) (target memory : State) :
    ∀ steps,
      emaRun (effectiveDecay rate alpha)
          (List.replicate steps target) memory =
        meanIterate rate alpha target steps memory
  | 0 => rfl
  | steps + 1 => by
      simp only [List.replicate_succ, emaRun_cons, meanIterate_succ]
      rw [← bernoulliMean_eq_emaUpdate_effectiveDecay]
      rw [emaRun_replicate_effectiveDecay_eq_meanIterate
        rate alpha target
        (bernoulliMean rate alpha memory target) steps]
      exact meanIterate_bernoulliMean rate alpha target memory steps

end MeanBridge

section MechanismBoundary

variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- A genuinely random update coin, non-unit decay, and a displaced target
give strictly positive stochastic branch variance. -/
theorem branchVariance_positive
    (rate alpha : ℝ) (memory target : State)
    (rate_positive : 0 < rate)
    (rate_lt_one : rate < 1)
    (alpha_lt_one : alpha < 1)
    (target_ne_memory : target ≠ memory) :
    0 < branchVariance rate alpha memory target := by
  rw [branchVariance_eq rate alpha memory target
    (le_of_lt rate_positive) (le_of_lt rate_lt_one)
    (le_of_lt alpha_lt_one)]
  have target_sub_memory_ne_zero : target - memory ≠ 0 :=
    sub_ne_zero.mpr target_ne_memory
  have norm_positive : 0 < ‖target - memory‖ :=
    norm_pos_iff.mpr target_sub_memory_ne_zero
  positivity

/-- Negative boundary: stochasticity is unobservable when the memory already
equals the target. -/
theorem branchVariance_fixed_target_zero
    (rate alpha : ℝ) (target : State) :
    branchVariance rate alpha target target = 0 := by
  have ema_fixed : emaUpdate alpha target target = target := by
    rw [emaUpdate_eq_interpolation]
    simp
  simp [branchVariance, branchUpdate, bernoulliMean_fixed, ema_fixed]

end MechanismBoundary

/-! ## Executable correspondence fixture -/

/-- Update probability one-half and source decay one-half have effective
deterministic decay three-quarters.  Both means agree, while the stochastic
branch variance remains positive away from the target. -/
theorem half_rate_half_decay :
    effectiveDecay (1 / 2) (1 / 2) = (3 / 4 : ℝ) ∧
      bernoulliMean (1 / 2) (1 / 2) (0 : ℝ) 1 =
        emaUpdate (3 / 4) (0 : ℝ) 1 ∧
      branchVariance (1 / 2) (1 / 2) (0 : ℝ) 1 = 1 / 16 := by
  norm_num
    [effectiveDecay, effectiveGain, bernoulliMean, emaUpdate,
      branchVariance, branchUpdate, Real.norm_eq_abs]

/-- Positive moving-target fixture: the exact mean bridge follows two
different working-model checkpoints in chronological order. -/
theorem moving_target_mean_bridge :
    bernoulliMeanRun (1 / 2) (1 / 2) [(4 : ℝ), 8] 0 =
        (11 / 4 : ℝ) ∧
      emaRun (3 / 4) [(4 : ℝ), 8] 0 = (11 / 4 : ℝ) := by
  norm_num
    [bernoulliMeanRun, bernoulliMean, emaUpdate, emaRun]

end

end SemanticMemoryTemporalBridge

end Mettapedia.MachineLearning.ContinualLearning

#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.bernoulliMean_eq_emaUpdate_effectiveDecay
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.bernoulliMeanRun_eq_emaRun_effectiveDecay
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.bernoulliMeanRun_norm_sub_le_discounted
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.emaRun_replicate_effectiveDecay_eq_meanIterate
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.branchVariance_positive
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.branchVariance_fixed_target_zero
#print axioms Mettapedia.MachineLearning.ContinualLearning.SemanticMemoryTemporalBridge.half_rate_half_decay
