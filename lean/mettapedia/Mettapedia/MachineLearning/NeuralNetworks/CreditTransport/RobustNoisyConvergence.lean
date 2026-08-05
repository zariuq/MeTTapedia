import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint

/-!
# Robust convergence under additive solver noise

Aybat, Fallah, Gürbüzbalaban, and Özdaglar, *Robust Accelerated Gradient
Methods for Smooth Strongly Convex Functions* (arXiv:1805.10579), derive
rate--robustness bounds for first-order methods under additive gradient noise.
The local source artifact has SHA-256
`447b0ca92abe6c01627a491ac125d61056bcea4f0f1a226d722a30d1c4c08787`.

This file isolates and generalizes the recurrence behind source Equation
(59).  A one-step storage inequality may contain both a hard-IQC supply and
an additive noise budget.  Exact finite-horizon telescoping separates their
effects: hard-IQC credit can be discarded, whereas noise accumulates through
the same chronological discount kernel.  Constant noise yields the familiar
geometric transient plus a nonzero robustness floor.

The result is trace-level.  It does not infer zero mean, independence,
covariance, a positive-semidefinite storage matrix, or the matrix inequalities
used by the source.  Those are distinct runtime or probabilistic obligations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RobustNoisyConvergence

open IntegralQuadraticConstraint

noncomputable section

/-! ## Noisy storage telescoping -/

/-- One-step storage inequality with a hard-IQC supply and an additive
per-step noise budget. -/
def DissipatesWithSupplyAndNoise
    (rate multiplier : ℝ)
    (storage supply noise : ℕ → ℝ) : Prop :=
  ∀ step,
    storage (step + 1) - rate * storage step +
        multiplier * supply step ≤
      noise step

/-- The exact finite-horizon noisy analogue of the IQC storage telescope. -/
theorem accumulated_storage_supply_le_discountedNoise
    {rate multiplier : ℝ}
    (rateNonnegative : 0 ≤ rate)
    {storage supply noise : ℕ → ℝ}
    (dissipates :
      DissipatesWithSupplyAndNoise
        rate multiplier storage supply noise)
    (horizon : ℕ) :
    storage horizon - rate ^ horizon * storage 0 +
        multiplier * discountedSupply rate supply horizon ≤
      discountedSupply rate noise horizon := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, discountedSupply_succ, pow_succ]
      calc
        storage (horizon + 1) -
              rate ^ horizon * rate * storage 0 +
              multiplier *
                (rate * discountedSupply rate supply horizon +
                  supply horizon) =
            (storage (horizon + 1) - rate * storage horizon +
                multiplier * supply horizon) +
              rate *
                (storage horizon - rate ^ horizon * storage 0 +
                  multiplier *
                    discountedSupply rate supply horizon) := by
              ring
        _ ≤ noise horizon +
              rate * discountedSupply rate noise horizon :=
          add_le_add (dissipates horizon)
            (mul_le_mul_of_nonneg_left
              inductionHypothesis rateNonnegative)
        _ = discountedSupply rate noise (horizon + 1) := by
          rw [discountedSupply_succ]
          ring

/-- Hard-IQC credit removes the supply term but cannot remove the accumulated
noise term. -/
theorem storage_le_geometric_add_discountedNoise
    {rate multiplier : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply noise : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupplyAndNoise
        rate multiplier storage supply noise)
    (horizon : ℕ) :
    storage horizon ≤
      rate ^ horizon * storage 0 +
        discountedSupply rate noise horizon := by
  have accumulated :=
    accumulated_storage_supply_le_discountedNoise
      rateNonnegative dissipates horizon
  have weightedSupplyNonnegative :
      0 ≤ multiplier * discountedSupply rate supply horizon :=
    mul_nonneg multiplierNonnegative (hard horizon)
  linarith

/-! ## Monotonicity and constant-noise closed form -/

theorem discountedSupply_mono
    {rate : ℝ} (rateNonnegative : 0 ≤ rate)
    {left right : ℕ → ℝ}
    (pointwise : ∀ step, left step ≤ right step)
    (horizon : ℕ) :
    discountedSupply rate left horizon ≤
      discountedSupply rate right horizon := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, discountedSupply_succ]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          inductionHypothesis rateNonnegative)
        (pointwise horizon)

/-- Exact chronological accumulation of a constant noise budget. -/
theorem discountedSupply_const_closedForm
    {rate injectedNoise : ℝ}
    (rateNeOne : rate ≠ 1)
    (horizon : ℕ) :
    discountedSupply rate (fun _ => injectedNoise) horizon =
      injectedNoise * (1 - rate ^ horizon) / (1 - rate) := by
  have denominatorNeZero : 1 - rate ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm rateNeOne)
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, inductionHypothesis, pow_succ]
      field_simp [denominatorNeZero]
      ring

/-- The asymptotic storage floor induced by a constant additive noise
budget. -/
def noiseFloor (rate injectedNoise : ℝ) : ℝ :=
  injectedNoise / (1 - rate)

theorem geometric_add_noise_eq_floor_form
    {rate injectedNoise initial : ℝ}
    (rateNeOne : rate ≠ 1)
    (horizon : ℕ) :
    rate ^ horizon * initial +
          injectedNoise * (1 - rate ^ horizon) / (1 - rate) =
      rate ^ horizon * (initial - noiseFloor rate injectedNoise) +
        noiseFloor rate injectedNoise := by
  have denominatorNeZero : 1 - rate ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm rateNeOne)
  simp only [noiseFloor]
  field_simp [denominatorNeZero]
  ring

/-- Source Equation (59), generalized from a constant covariance-derived
term to any scalar trace satisfying the declared noisy dissipation
inequality. -/
theorem storage_le_geometric_add_constantNoise
    {rate multiplier injectedNoise : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (rateLtOne : rate < 1)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupplyAndNoise rate multiplier storage supply
        (fun _ => injectedNoise))
    (horizon : ℕ) :
    storage horizon ≤
      rate ^ horizon * storage 0 +
        injectedNoise * (1 - rate ^ horizon) / (1 - rate) := by
  calc
    storage horizon ≤
        rate ^ horizon * storage 0 +
          discountedSupply rate (fun _ => injectedNoise) horizon :=
      storage_le_geometric_add_discountedNoise
        rateNonnegative multiplierNonnegative hard dissipates horizon
    _ = rate ^ horizon * storage 0 +
          injectedNoise * (1 - rate ^ horizon) / (1 - rate) := by
      rw [discountedSupply_const_closedForm (ne_of_lt rateLtOne)]

/-- Constant-noise convergence is contraction of the excess above the noise
floor, not convergence to zero. -/
theorem storage_sub_noiseFloor_le
    {rate multiplier injectedNoise : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (rateLtOne : rate < 1)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupplyAndNoise rate multiplier storage supply
        (fun _ => injectedNoise))
    (horizon : ℕ) :
    storage horizon - noiseFloor rate injectedNoise ≤
      rate ^ horizon *
        (storage 0 - noiseFloor rate injectedNoise) := by
  have bound :=
    storage_le_geometric_add_constantNoise
      rateNonnegative rateLtOne multiplierNonnegative
      hard dissipates horizon
  rw [geometric_add_noise_eq_floor_form
    (ne_of_lt rateLtOne)] at bound
  linarith

/-- If the initial storage is already below the robustness floor, the same
one-step certificate keeps every later storage below that floor. -/
theorem storage_le_noiseFloor_of_initial_le
    {rate multiplier injectedNoise : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (rateLtOne : rate < 1)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply : ℕ → ℝ}
    (initialBelow :
      storage 0 ≤ noiseFloor rate injectedNoise)
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupplyAndNoise rate multiplier storage supply
        (fun _ => injectedNoise))
    (horizon : ℕ) :
    storage horizon ≤ noiseFloor rate injectedNoise := by
  have excessBound :=
    storage_sub_noiseFloor_le
      rateNonnegative rateLtOne multiplierNonnegative
      hard dissipates horizon
  have contractedInitialNonpositive :
      rate ^ horizon *
          (storage 0 - noiseFloor rate injectedNoise) ≤
        0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (pow_nonneg rateNonnegative horizon)
      (sub_nonpos.mpr initialBelow)
  linarith

/-- A uniform pointwise noise ceiling supplies the same closed-form
robustness floor even when the actual noise budget varies over time. -/
theorem storage_le_geometric_add_uniformNoise
    {rate multiplier noiseBudget : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (rateLtOne : rate < 1)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply noise : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (noiseUpper : ∀ step, noise step ≤ noiseBudget)
    (dissipates :
      DissipatesWithSupplyAndNoise
        rate multiplier storage supply noise)
    (horizon : ℕ) :
    storage horizon ≤
      rate ^ horizon * storage 0 +
        noiseBudget * (1 - rate ^ horizon) / (1 - rate) := by
  calc
    storage horizon ≤
        rate ^ horizon * storage 0 +
          discountedSupply rate noise horizon :=
      storage_le_geometric_add_discountedNoise
        rateNonnegative multiplierNonnegative hard dissipates horizon
    _ ≤ rate ^ horizon * storage 0 +
          discountedSupply rate (fun _ => noiseBudget) horizon :=
      by
        simpa [add_comm] using
          add_le_add_left
            (discountedSupply_mono rateNonnegative noiseUpper horizon)
            (rate ^ horizon * storage 0)
    _ = rate ^ horizon * storage 0 +
          noiseBudget * (1 - rate ^ horizon) / (1 - rate) := by
      rw [discountedSupply_const_closedForm (ne_of_lt rateLtOne)]

/-! ## Positive and negative boundaries -/

def zeroSupply : ℕ → ℝ := fun _ => 0

def constantFloorStorage (rate injectedNoise : ℝ) : ℕ → ℝ :=
  fun _ => noiseFloor rate injectedNoise

theorem noiseFloor_balance
    {rate injectedNoise : ℝ}
    (rateNeOne : rate ≠ 1) :
    noiseFloor rate injectedNoise =
      rate * noiseFloor rate injectedNoise + injectedNoise := by
  have denominatorNeZero : 1 - rate ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm rateNeOne)
  simp only [noiseFloor]
  field_simp [denominatorNeZero]
  ring

theorem zeroSupply_is_hard
    {rate : ℝ} (rateNonnegative : 0 ≤ rate) :
    RhoHardIQC rate zeroSupply :=
  rhoHard_of_pointwise rateNonnegative (fun _ => le_rfl)

theorem constantFloorStorage_dissipates
    {rate multiplier injectedNoise : ℝ}
    (rateNeOne : rate ≠ 1) :
    DissipatesWithSupplyAndNoise rate multiplier
      (constantFloorStorage rate injectedNoise) zeroSupply
      (fun _ => injectedNoise) := by
  intro step
  simp only [constantFloorStorage, zeroSupply]
  have balance :=
    noiseFloor_balance
      (rate := rate) (injectedNoise := injectedNoise) rateNeOne
  linarith

/-- Faster deterministic contraction can have a worse stochastic robustness
floor. Rate alone therefore cannot select an accelerated profile. -/
theorem faster_rate_can_have_larger_noise_floor :
    (1 / 4 : ℝ) < 1 / 2 ∧
      noiseFloor (1 / 2) 1 < noiseFloor (1 / 4) 3 := by
  norm_num [noiseFloor]

/-- A positive additive noise budget admits a positive exact stationary
storage. The noisy theorem cannot be strengthened to convergence to zero. -/
theorem positive_noise_has_nonzero_stationary_storage :
    noiseFloor (1 / 2) 1 = 2 ∧
      DissipatesWithSupplyAndNoise (1 / 2) 1
        (constantFloorStorage (1 / 2) 1) zeroSupply (fun _ => 1) := by
  constructor
  · norm_num [noiseFloor]
  · exact constantFloorStorage_dissipates (by norm_num)

end

end RobustNoisyConvergence

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.accumulated_storage_supply_le_discountedNoise
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.storage_le_geometric_add_constantNoise
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.storage_sub_noiseFloor_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.storage_le_geometric_add_uniformNoise
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.faster_rate_can_have_larger_noise_floor
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RobustNoisyConvergence.positive_noise_has_nonzero_stationary_storage
