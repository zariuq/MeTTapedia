import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyChartFork
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-Energy Chart Fork on the Shared Mode State

This file tests a more manuscript-shaped radial profile on the same `ModeState`.
It replaces the raw squared Sobolev energy by the smoother quantity
`log (1 + energy)`.

* The soft log-energy radius lands on the good side: it is continuous and
  truncation-friendly because `log (1 + u) <= u`.
* The hard-side analogue asking whether `log (1 + energy) > 0` still lands on
  the bad side: it is tail-spike stable but disagrees at `modeZero`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateLogEnergyChartFork

/-- Soft log-energy term on the shared mode space. -/
def logEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) * sobolevEnergyWeight m n

/-- Soft log-energy radius. -/
def logEnergyRadius (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, logEnergyTerm m x n

/-- Zeroth visible mode plus the soft log-energy radius. -/
def logEnergyStatistic (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + logEnergyRadius m x

/-- Hard log-energy detector. -/
def hardLogEnergyThresholdRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, 0 < Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) then 1 else 0

theorem continuous_logEnergyTerm (m n : ℕ) :
    Continuous fun x : ModeState => logEnergyTerm m x n := by
  have harg : Continuous fun x : ModeState =>
      1 + (sobolevAmplification m x n) ^ (2 : ℕ) := by
    exact continuous_const.add ((continuous_sobolevAmplification m n).pow 2)
  have hlog : Continuous fun x : ModeState =>
      Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) := by
    refine harg.log ?_
    intro x
    positivity
  simpa [logEnergyTerm] using
    hlog.mul (continuous_const : Continuous fun _ : ModeState => sobolevEnergyWeight m n)

theorem logEnergyTerm_le_sobolevEnergyTerm (m : ℕ) (x : ModeState) (n : ℕ) :
    logEnergyTerm m x n ≤ sobolevEnergyTerm m x n := by
  have harg_pos : 0 < 1 + (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
  have hlog_le :
      Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ))
        ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by
    have h := Real.log_le_sub_one_of_pos harg_pos
    linarith
  exact mul_le_mul_of_nonneg_right hlog_le (sobolevEnergyWeight_nonneg m n)

theorem norm_logEnergyTerm_le_inverseSquare (m : ℕ) (x : ModeState) (n : ℕ) :
    ‖logEnergyTerm m x n‖ ≤ inverseSquareModeWeights.weight n := by
  have hlog_nonneg :
      0 ≤ Real.log (1 + (sobolevAmplification m x n) ^ (2 : ℕ)) := by
    have hsq_nonneg : 0 ≤ (sobolevAmplification m x n) ^ (2 : ℕ) := by positivity
    apply Real.log_nonneg
    nlinarith
  have hterm_nonneg : 0 ≤ logEnergyTerm m x n := by
    exact mul_nonneg hlog_nonneg (sobolevEnergyWeight_nonneg m n)
  have hsob_nonneg : 0 ≤ sobolevEnergyTerm m x n := by
    exact mul_nonneg (by positivity) (sobolevEnergyWeight_nonneg m n)
  calc
    ‖logEnergyTerm m x n‖ = logEnergyTerm m x n := by
      rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    _ ≤ sobolevEnergyTerm m x n := logEnergyTerm_le_sobolevEnergyTerm m x n
    _ ≤ inverseSquareModeWeights.weight n := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hsob_nonneg] using
        norm_sobolevEnergyTerm_le_inverseSquare m x n

theorem continuous_logEnergyRadius (m : ℕ) :
    Continuous (logEnergyRadius m) := by
  unfold logEnergyRadius
  refine continuous_tsum (fun n => continuous_logEnergyTerm m n)
    inverseSquareModeWeights.summable_weight ?_
  intro n x
  exact norm_logEnergyTerm_le_inverseSquare m x n

theorem continuous_logEnergyStatistic (m : ℕ) :
    Continuous (logEnergyStatistic m) := by
  unfold logEnergyStatistic
  exact (continuous_coeffObservable 0).add (continuous_logEnergyRadius m)

theorem tendsto_logEnergyRadius_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => logEnergyRadius m (truncateModes N x))
      Filter.atTop (nhds (logEnergyRadius m x)) := by
  exact (continuous_logEnergyRadius m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_logEnergyStatistic_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => logEnergyStatistic m (truncateModes N x))
      Filter.atTop (nhds (logEnergyStatistic m x)) := by
  exact (continuous_logEnergyStatistic m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_logEnergy_cutoffPotential
    (m : ℕ) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (logEnergyRadius m) (logEnergyStatistic m)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_logEnergyRadius m) (continuous_logEnergyStatistic m)

theorem continuous_logEnergy_coleHopfPhi
    (m : ℕ) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (logEnergyRadius m) (logEnergyStatistic m))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_logEnergyRadius m) (continuous_logEnergyStatistic m)

theorem hardLogEnergyThresholdRadius_tailSpikeStableAt_one (m : ℕ) :
    TailSpikeStableAt (hardLogEnergyThresholdRadius m) 1 := by
  intro N
  unfold hardLogEnergyThresholdRadius
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨N, ?_⟩
    have hsq_pos : 0 < (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by positivity
    have harg_gt_one : 1 < 1 + (((N + 1 : ℝ) ^ m) ^ (2 : ℕ)) := by linarith
    have hlog_pos :
        0 < Real.log (1 + (((N + 1 : ℝ) ^ m) ^ (2 : ℕ))) := by
      exact Real.log_pos harg_gt_one
    simpa [sobolevAmplification, tailSpikeMode] using hlog_pos

theorem hardLogEnergyThresholdRadius_modeZero (m : ℕ) :
    hardLogEnergyThresholdRadius m modeZero = 0 := by
  unfold hardLogEnergyThresholdRadius
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    simp [sobolevAmplification, modeZero] at hn
  · rfl

theorem not_continuousAt_hardLogEnergyThresholdRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardLogEnergyThresholdRadius m) modeZero := by
  refine not_continuousAt_of_tailSpikeStableAt
    (hardLogEnergyThresholdRadius_tailSpikeStableAt_one m) ?_
  simp [hardLogEnergyThresholdRadius_modeZero]

theorem not_continuousAt_hardLogEnergyThreshold_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardLogEnergyThresholdRadius m) unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    (hardLogEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold cutoffPotential
      rw [hardLogEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardLogEnergyThreshold_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1
        (cutoffPotential (fun r => r) (hardLogEnergyThresholdRadius m) unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    (hardLogEnergyThresholdRadius_tailSpikeStableAt_one m)
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold cutoffPotential
      rw [hardLogEnergyThresholdRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

end ModeStateLogEnergyChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
