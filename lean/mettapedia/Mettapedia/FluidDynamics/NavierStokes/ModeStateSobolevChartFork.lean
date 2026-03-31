import Mettapedia.FluidDynamics.NavierStokes.ModeStateChartFork
import Mathlib.Analysis.PSeries

/-!
# Sobolev-Style Chart Fork on the Shared Mode State

This file moves one step closer to manuscript shape. We amplify high modes by a
polynomial Sobolev-style factor `((n+1)^m)` before applying the chart cutoff.

* The soft version, using the bounded scalar `|t| / (1 + |t|)` together with a
  concrete inverse-square envelope, lands on the good side.
* The hard version, which only records whether any amplified mode is nonzero,
  collapses to the earlier hard support detector and lands on the bad side.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateSobolevChartFork

/-- Concrete inverse-square envelope on mode index. -/
def inverseSquareModeWeights : SummableModeWeights where
  weight n := 1 / ((n + 1 : ℝ) ^ (2 : ℕ))
  summable_weight := by
    simpa using (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  weight_nonneg := by
    intro n
    positivity

/-- Polynomial Sobolev-style amplification of the `n`-th mode. -/
def sobolevAmplification (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ m) * x.coeff n

/-- Soft Sobolev-weighted mode contribution. -/
def softSobolevTerm (m : ℕ) (x : ModeState) (n : ℕ) : ℝ :=
  softSupportScalar (sobolevAmplification m x n) * inverseSquareModeWeights.weight n

/-- Soft Sobolev chart radius. -/
def softSobolevRadius (m : ℕ) (x : ModeState) : ℝ :=
  ∑' n, softSobolevTerm m x n

/-- Zeroth visible mode plus the soft Sobolev radius. -/
def softSobolevStatistic (m : ℕ) (x : ModeState) : ℝ :=
  x.coeff 0 + softSobolevRadius m x

/-- Hard Sobolev chart radius: any nonzero amplified mode is counted as present. -/
def hardSobolevRadius (m : ℕ) (x : ModeState) : ℝ :=
  if ∃ n, sobolevAmplification m x n ≠ 0 then 1 else 0

theorem continuous_sobolevAmplification (m n : ℕ) :
    Continuous fun x : ModeState => sobolevAmplification m x n := by
  simpa [sobolevAmplification] using
    (continuous_const : Continuous fun _ : ModeState => ((n + 1 : ℝ) ^ m)).mul
      (continuous_coeffObservable n)

theorem continuous_softSobolevTerm (m n : ℕ) :
    Continuous fun x : ModeState => softSobolevTerm m x n := by
  simpa [softSobolevTerm] using
    (continuous_softSupportScalar.comp (continuous_sobolevAmplification m n)).mul
      (continuous_const : Continuous fun _ : ModeState => inverseSquareModeWeights.weight n)

theorem norm_softSobolevTerm_le (m : ℕ) (x : ModeState) (n : ℕ) :
    ‖softSobolevTerm m x n‖ ≤ inverseSquareModeWeights.weight n := by
  have hterm_nonneg : 0 ≤ softSobolevTerm m x n := by
    exact mul_nonneg
      (softSupportScalar_nonneg (sobolevAmplification m x n))
      (inverseSquareModeWeights.weight_nonneg n)
  calc
    ‖softSobolevTerm m x n‖ = softSobolevTerm m x n := by
      simp [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    _ = softSupportScalar (sobolevAmplification m x n) * inverseSquareModeWeights.weight n := rfl
    _ ≤ inverseSquareModeWeights.weight n := by
      nlinarith [softSupportScalar_nonneg (sobolevAmplification m x n),
        softSupportScalar_le_one (sobolevAmplification m x n),
        inverseSquareModeWeights.weight_nonneg n]

theorem continuous_softSobolevRadius (m : ℕ) :
    Continuous (softSobolevRadius m) := by
  unfold softSobolevRadius
  refine continuous_tsum (fun n => continuous_softSobolevTerm m n)
    inverseSquareModeWeights.summable_weight ?_
  intro n x
  exact norm_softSobolevTerm_le m x n

theorem continuous_softSobolevStatistic (m : ℕ) :
    Continuous (softSobolevStatistic m) := by
  unfold softSobolevStatistic
  exact (continuous_coeffObservable 0).add (continuous_softSobolevRadius m)

theorem tendsto_softSobolevRadius_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => softSobolevRadius m (truncateModes N x))
      Filter.atTop (nhds (softSobolevRadius m x)) := by
  exact (continuous_softSobolevRadius m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_softSobolevStatistic_truncateModes (m : ℕ) (x : ModeState) :
    Tendsto (fun N => softSobolevStatistic m (truncateModes N x))
      Filter.atTop (nhds (softSobolevStatistic m x)) := by
  exact (continuous_softSobolevStatistic m).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_softSobolev_cutoffPotential
    (m : ℕ) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (softSobolevRadius m) (softSobolevStatistic m)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_softSobolevRadius m) (continuous_softSobolevStatistic m)

theorem continuous_softSobolev_coleHopfPhi
    (m : ℕ) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (softSobolevRadius m) (softSobolevStatistic m))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_softSobolevRadius m) (continuous_softSobolevStatistic m)

theorem hardSobolevRadius_eq_hardSupportRadius (m : ℕ) :
    hardSobolevRadius m = hardSupportRadius := by
  funext x
  have hiff : (∃ n, sobolevAmplification m x n ≠ 0) ↔ ∃ n, x.coeff n ≠ 0 := by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      intro hzero
      apply hn
      simp [sobolevAmplification, hzero]
    · intro h
      rcases h with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hfac : ((n + 1 : ℝ) ^ m) ≠ 0 := by positivity
      simpa [sobolevAmplification] using mul_ne_zero hfac hn
  by_cases h : ∃ n, x.coeff n ≠ 0
  · have hs : ∃ n, sobolevAmplification m x n ≠ 0 := hiff.mpr h
    simp [hardSobolevRadius, hardSupportRadius, tailPresenceRadius, hs, h]
  · have hs : ¬ ∃ n, sobolevAmplification m x n ≠ 0 := by
      intro hs
      exact h (hiff.mp hs)
    simp [hardSobolevRadius, hardSupportRadius, tailPresenceRadius, hs, h]

theorem not_continuousAt_hardSobolevRadius_modeZero (m : ℕ) :
    ¬ ContinuousAt (hardSobolevRadius m) modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupportRadius_modeZero

theorem not_continuousAt_hardSobolev_cutoffPotential_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) (hardSobolevRadius m) unitStatisticMode)
      modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupport_cutoffPotential_modeZero

theorem not_continuousAt_hardSobolev_coleHopfPhi_modeZero (m : ℕ) :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) (hardSobolevRadius m) unitStatisticMode))
      modeZero := by
  rw [hardSobolevRadius_eq_hardSupportRadius m]
  exact not_continuousAt_hardSupport_coleHopfPhi_modeZero

end ModeStateSobolevChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
