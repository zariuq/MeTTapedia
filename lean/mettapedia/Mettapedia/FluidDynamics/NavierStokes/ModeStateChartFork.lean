import Mettapedia.FluidDynamics.NavierStokes.ModeStateObservableClass
import Mettapedia.FluidDynamics.NavierStokes.ModeStateTailSensitivityObstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Chart Fork on the Shared Mode State

This file forces a concrete chart-style fork on the shared `ModeState`.

* A soft support observable, built from the continuous scalar
  `|t| / (1 + |t|)` and summable mode weights, lies on the good side: it is
  continuous and truncation-friendly.
* A hard support observable, recording whether any coefficient is nonzero, lies
  on the bad side: it is not continuous at `modeZero`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateChartFork

/-- Continuous soft support detector on one real coordinate. -/
def softSupportScalar : ℝ → ℝ :=
  fun t => |t| / (1 + |t|)

/-- Soft weighted mode contribution. -/
def softSupportTerm (W : SummableModeWeights) (x : ModeState) (n : ℕ) : ℝ :=
  softSupportScalar (x.coeff n) * W.weight n

/-- Soft support chart radius. -/
def softSupportRadius (W : SummableModeWeights) (x : ModeState) : ℝ :=
  ∑' n, softSupportTerm W x n

/-- Zeroth visible mode plus the soft support radius. -/
def softSupportStatistic (W : SummableModeWeights) (x : ModeState) : ℝ :=
  x.coeff 0 + softSupportRadius W x

/-- Hard support chart radius: any nonzero mode is counted as present. -/
def hardSupportRadius : ModeState → ℝ :=
  tailPresenceRadius

theorem continuous_softSupportScalar :
    Continuous softSupportScalar := by
  have hden : ∀ t : ℝ, 1 + |t| ≠ 0 := by
    intro t
    positivity
  simpa [softSupportScalar] using
    continuous_abs.div (continuous_const.add continuous_abs) hden

theorem softSupportScalar_nonneg (t : ℝ) :
    0 ≤ softSupportScalar t := by
  unfold softSupportScalar
  positivity

theorem softSupportScalar_le_one (t : ℝ) :
    softSupportScalar t ≤ 1 := by
  have hnonneg : 0 ≤ |t| := abs_nonneg t
  have hle : |t| ≤ 1 + |t| := by linarith
  have hden : 0 < 1 + |t| := by positivity
  have hdiv : |t| / (1 + |t|) ≤ 1 := by
    rw [_root_.div_le_iff₀ hden]
    linarith
  simpa [softSupportScalar] using hdiv

theorem continuous_softSupportTerm (W : SummableModeWeights) (n : ℕ) :
    Continuous fun x : ModeState => softSupportTerm W x n := by
  simpa [softSupportTerm] using
    (continuous_softSupportScalar.comp (continuous_coeffObservable n)).mul
      (continuous_const : Continuous fun _ : ModeState => W.weight n)

theorem norm_softSupportTerm_le (W : SummableModeWeights) (x : ModeState) (n : ℕ) :
    ‖softSupportTerm W x n‖ ≤ W.weight n := by
  have hterm_nonneg : 0 ≤ softSupportTerm W x n := by
    exact mul_nonneg (softSupportScalar_nonneg (x.coeff n)) (W.weight_nonneg n)
  calc
    ‖softSupportTerm W x n‖ = softSupportTerm W x n := by
      simp [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
    _ = softSupportScalar (x.coeff n) * W.weight n := rfl
    _ ≤ W.weight n := by
      nlinarith [softSupportScalar_nonneg (x.coeff n), softSupportScalar_le_one (x.coeff n),
        W.weight_nonneg n]

theorem continuous_softSupportRadius (W : SummableModeWeights) :
    Continuous (softSupportRadius W) := by
  unfold softSupportRadius
  refine continuous_tsum (fun n => continuous_softSupportTerm W n) W.summable_weight ?_
  intro n x
  exact norm_softSupportTerm_le W x n

theorem continuous_softSupportStatistic (W : SummableModeWeights) :
    Continuous (softSupportStatistic W) := by
  unfold softSupportStatistic
  exact (continuous_coeffObservable 0).add (continuous_softSupportRadius W)

theorem tendsto_softSupportRadius_truncateModes (W : SummableModeWeights) (x : ModeState) :
    Tendsto (fun N => softSupportRadius W (truncateModes N x))
      Filter.atTop (nhds (softSupportRadius W x)) := by
  exact (continuous_softSupportRadius W).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_softSupportStatistic_truncateModes (W : SummableModeWeights) (x : ModeState) :
    Tendsto (fun N => softSupportStatistic W (truncateModes N x))
      Filter.atTop (nhds (softSupportStatistic W x)) := by
  exact (continuous_softSupportStatistic W).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_softSupport_cutoffPotential
    (W : SummableModeWeights) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (softSupportRadius W) (softSupportStatistic W)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_softSupportRadius W) (continuous_softSupportStatistic W)

theorem continuous_softSupport_coleHopfPhi
    (W : SummableModeWeights) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (softSupportRadius W) (softSupportStatistic W))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_softSupportRadius W) (continuous_softSupportStatistic W)

theorem not_continuousAt_hardSupportRadius_modeZero :
    ¬ ContinuousAt hardSupportRadius modeZero := by
  exact not_continuousAt_tailPresenceRadius_modeZero

theorem not_continuousAt_hardSupport_cutoffPotential_modeZero :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) hardSupportRadius unitStatisticMode)
      modeZero := by
  exact not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    tailPresenceRadius_tailSpikeStableAt_one
    tendsto_unitStatisticMode_tailSpikeMode
    (by
      unfold hardSupportRadius cutoffPotential
      rw [tailPresenceRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

theorem not_continuousAt_hardSupport_coleHopfPhi_modeZero :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) hardSupportRadius unitStatisticMode))
      modeZero := by
  exact not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    tailPresenceRadius_tailSpikeStableAt_one
    tendsto_unitStatisticMode_tailSpikeMode
    (by norm_num)
    (by
      unfold hardSupportRadius cutoffPotential
      rw [tailPresenceRadius_modeZero]
      norm_num [unitStatisticMode, modeZero])

end ModeStateChartFork

end NavierStokes
end FluidDynamics
end Mettapedia
