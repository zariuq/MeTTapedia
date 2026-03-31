import Mettapedia.FluidDynamics.NavierStokes.ModeStateSobolevChartFork
import Mathlib.Analysis.PSeries

/-!
# Energy-Style Chart Fork on the Shared Mode State

This file adds a more energy-like chart family. High modes are amplified by the
Sobolev-style polynomial factor `((n+1)^m)` and then squared.

* The soft energy radius uses a compensating inverse-power envelope and lands on
  the good side: it is continuous and truncation-friendly.
* The hard energy threshold detector lands on the bad side: it is stable on the
  remote spike family but disagrees at `modeZero`, so it is not continuous.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyChartFork

/-- Inverse-power envelope compensating the Sobolev amplification. -/
def sobolevEnergyWeight (m n : ℕ) : ℝ :=
  1 / ((n + 1 : ℝ) ^ (2 * m + 2 : ℕ))

/-- Soft energy term: squared amplified mode with the compensating weight. -/
def sobolevEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  (sobolevAmplification m x n) ^ (2 : ℕ) * sobolevEnergyWeight m n

/-- Soft energy radius. -/
def sobolevEnergyRadius (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, sobolevEnergyTerm m x n

/-- Zeroth visible mode plus the soft energy radius. -/
def sobolevEnergyStatistic (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + sobolevEnergyRadius m x

/-- Hard energy threshold detector. -/
def hardEnergyThresholdRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 1 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) then 1 else 0

theorem summable_sobolevEnergyWeight (m : ℕ) :
    Summable (fun n : ℕ => sobolevEnergyWeight m n) := by
  have hm : 1 < 2 * m + 2 := by omega
  simpa [sobolevEnergyWeight] using
    (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 * m + 2 : ℕ)) 1).2
      (Real.summable_one_div_nat_pow.mpr hm)

theorem sobolevEnergyWeight_nonneg (m n : ℕ) :
    0 ≤ sobolevEnergyWeight m n := by
  unfold sobolevEnergyWeight
  positivity

theorem continuous_sobolevEnergyTerm (m n : ℕ) :
    Continuous fun x : ModeState => sobolevEnergyTerm m x n := by
  simpa [sobolevEnergyTerm] using
    ((continuous_sobolevAmplification m n).pow 2).mul
      (continuous_const : Continuous fun _ : ModeState => sobolevEnergyWeight m n)

theorem sobolevEnergyTerm_eq_inverseSquareScaled (m : ℕ) (x : ModeState) (n : ℕ) :
    sobolevEnergyTerm m x n = (x.coeff n) ^ (2 : ℕ) * inverseSquareModeWeights.weight n := by
  unfold sobolevEnergyTerm sobolevAmplification sobolevEnergyWeight inverseSquareModeWeights
  have h1 : ((n + 1 : ℝ) ^ (2 * m + 2 : ℕ)) ≠ 0 := by positivity
  have h2 : ((n + 1 : ℝ) ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

theorem norm_sobolevEnergyTerm_le_inverseSquare (m : ℕ) (x : ModeState) (n : ℕ) :
    ‖sobolevEnergyTerm m x n‖ ≤ inverseSquareModeWeights.weight n := by
  rw [sobolevEnergyTerm_eq_inverseSquareScaled]
  have hsq_nonneg : 0 ≤ (x.coeff n) ^ (2 : ℕ) := by positivity
  have hsq_le_one : (x.coeff n) ^ (2 : ℕ) ≤ 1 := by
    have hsq : (x.coeff n) ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) := by
      rw [sq_le_sq]
      simpa using x.abs_le_one n
    simpa using hsq
  have hw_nonneg : 0 ≤ inverseSquareModeWeights.weight n :=
    inverseSquareModeWeights.weight_nonneg n
  have hprod_nonneg :
      0 ≤ (x.coeff n) ^ (2 : ℕ) * inverseSquareModeWeights.weight n :=
    mul_nonneg hsq_nonneg hw_nonneg
  calc
    ‖(x.coeff n) ^ (2 : ℕ) * inverseSquareModeWeights.weight n‖
        = (x.coeff n) ^ (2 : ℕ) * inverseSquareModeWeights.weight n := by
            rw [Real.norm_eq_abs, abs_of_nonneg hprod_nonneg]
    _ ≤ 1 * inverseSquareModeWeights.weight n := by
      gcongr
    _ = inverseSquareModeWeights.weight n := by ring

theorem continuous_sobolevEnergyRadius (m : ℕ) :
    Continuous (sobolevEnergyRadius m) := by
  unfold sobolevEnergyRadius
  refine continuous_tsum (fun n => continuous_sobolevEnergyTerm m n)
    inverseSquareModeWeights.summable_weight ?_
  intro n x
  exact norm_sobolevEnergyTerm_le_inverseSquare m x n

theorem continuous_sobolevEnergyStatistic (m : ℕ) :
    Continuous (sobolevEnergyStatistic m) := by
  unfold sobolevEnergyStatistic
  exact (continuous_coeffObservable 0).add (continuous_sobolevEnergyRadius m)

theorem tendsto_sobolevEnergyRadius_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => sobolevEnergyRadius m (truncateModes N x))
      Filter.atTop (nhds (sobolevEnergyRadius m x)) := by
  exact (continuous_sobolevEnergyRadius m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_sobolevEnergyStatistic_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => sobolevEnergyStatistic m (truncateModes N x))
      Filter.atTop (nhds (sobolevEnergyStatistic m x)) := by
  exact (continuous_sobolevEnergyStatistic m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_sobolevEnergy_cutoffPotential
    (m : ℕ) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (sobolevEnergyRadius m) (sobolevEnergyStatistic m)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_sobolevEnergyRadius m) (continuous_sobolevEnergyStatistic m)

theorem continuous_sobolevEnergy_coleHopfPhi
    (m : ℕ) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (sobolevEnergyRadius m) (sobolevEnergyStatistic m))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_sobolevEnergyRadius m) (continuous_sobolevEnergyStatistic m)

theorem hardEnergyThresholdRadius_tailSpikeStableAt_one (m : ℕ) :
    TailSpikeStableAt (hardEnergyThresholdRadius m) 1 := by
  intro N
  unfold hardEnergyThresholdRadius
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨N, ?_⟩
    have hN1 : (1 : ℝ) ≤ (N + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hbase : 1 ≤ ((N + 1 : ℝ) ^ m) := by
      have hnat : 1 ≤ (N + 1) ^ m := by
        exact Nat.succ_le_of_lt (pow_pos (Nat.succ_pos N) m)
      exact_mod_cast hnat
    have hsquare : 1 ≤ (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by
      have hnonneg : 0 ≤ ((N + 1 : ℝ) ^ m) := by positivity
      calc
        1 = 1 * 1 := by ring
        _ ≤ ((N + 1 : ℝ) ^ m) * ((N + 1 : ℝ) ^ m) := by
          exact mul_le_mul hbase hbase (by positivity) hnonneg
        _ = (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by ring
    simpa [sobolevAmplification, tailSpikeMode] using hsquare

theorem hardEnergyThresholdRadius_modeZero (m : ℕ) :
    hardEnergyThresholdRadius m modeZero = 0 := by
  unfold hardEnergyThresholdRadius
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    simp [sobolevAmplification, modeZero] at hn
    linarith
  · rfl

theorem not_continuousAt_hardEnergyThresholdRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardEnergyThresholdRadius m) modeZero := by
  refine not_continuousAt_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m) ?_
  simp [hardEnergyThresholdRadius_modeZero]

theorem not_continuousAt_hardEnergyThreshold_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardEnergyThresholdRadius m) unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold cutoffPotential
      rw [hardEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardEnergyThreshold_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1
        (cutoffPotential (fun r => r) (hardEnergyThresholdRadius m) unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    (hardEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold cutoffPotential
      rw [hardEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

end ModeStateEnergyChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
