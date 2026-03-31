import Mettapedia.FluidDynamics.NavierStokes.ModeStateProductTopologyObstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Summable Observable Class on the Shared Mode State

This file packages a good class of observables on the shared `ModeState`
equipped with the coordinatewise product topology: nonnegative summable mode
weights. The associated weighted radius, derived statistic, cutoff potential,
and Cole-Hopf datum are continuous, and finite-mode truncations converge
through all of them.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateObservableClass

/-- Nonnegative summable mode weights define a good observable class on
`ModeState`. -/
structure SummableModeWeights where
  weight : ℕ → ℝ
  summable_weight : Summable weight
  weight_nonneg : ∀ n, 0 ≤ weight n

/-- Weighted `n`-th mode contribution. -/
def weightedModeTerm (W : SummableModeWeights) (x : ModeState) (n : ℕ) : ℝ :=
  |x.coeff n| * W.weight n

/-- Weighted radius observable. -/
def weightedModeRadius (W : SummableModeWeights) (x : ModeState) : ℝ :=
  ∑' n, weightedModeTerm W x n

/-- Zeroth visible mode plus the weighted radius. -/
def weightedModeStatistic (W : SummableModeWeights) (x : ModeState) : ℝ :=
  x.coeff 0 + weightedModeRadius W x

theorem continuous_coeffObservable (n : ℕ) :
    Continuous fun x : ModeState => x.coeff n := by
  exact (continuous_apply n).comp continuous_induced_dom

theorem continuous_weightedModeTerm (W : SummableModeWeights) (n : ℕ) :
    Continuous fun x : ModeState => weightedModeTerm W x n := by
  simpa [weightedModeTerm] using
    (continuous_abs.comp (continuous_coeffObservable n)).mul
      (continuous_const : Continuous fun _ : ModeState => W.weight n)

theorem norm_weightedModeTerm_le (W : SummableModeWeights) (x : ModeState) (n : ℕ) :
    ‖weightedModeTerm W x n‖ ≤ W.weight n := by
  calc
    ‖weightedModeTerm W x n‖ = weightedModeTerm W x n := by
      simp [weightedModeTerm, W.weight_nonneg n]
    _ = |x.coeff n| * W.weight n := rfl
    _ ≤ W.weight n := by
      nlinarith [x.abs_le_one n, W.weight_nonneg n]

theorem continuous_weightedModeRadius (W : SummableModeWeights) :
    Continuous (weightedModeRadius W) := by
  unfold weightedModeRadius
  refine continuous_tsum (fun n => continuous_weightedModeTerm W n) W.summable_weight ?_
  intro n x
  exact norm_weightedModeTerm_le W x n

theorem continuous_weightedModeStatistic (W : SummableModeWeights) :
    Continuous (weightedModeStatistic W) := by
  unfold weightedModeStatistic
  exact (continuous_coeffObservable 0).add (continuous_weightedModeRadius W)

theorem tendsto_weightedModeRadius_truncateModes (W : SummableModeWeights) (x : ModeState) :
    Tendsto (fun N => weightedModeRadius W (truncateModes N x))
      Filter.atTop (nhds (weightedModeRadius W x)) := by
  exact (continuous_weightedModeRadius W).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem tendsto_weightedModeStatistic_truncateModes (W : SummableModeWeights) (x : ModeState) :
    Tendsto (fun N => weightedModeStatistic W (truncateModes N x))
      Filter.atTop (nhds (weightedModeStatistic W x)) := by
  exact (continuous_weightedModeStatistic W).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x)

theorem continuous_weightedMode_cutoffPotential
    (W : SummableModeWeights) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W)) := by
  exact continuous_cutoffPotential hcutoff
    (continuous_weightedModeRadius W) (continuous_weightedModeStatistic W)

theorem continuous_weightedMode_coleHopfPhi
    (W : SummableModeWeights) {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν
      (cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W))) := by
  exact continuous_cutoffColeHopfPhi hcutoff
    (continuous_weightedModeRadius W) (continuous_weightedModeStatistic W)

theorem tendsto_weightedMode_cutoffPotential_truncateModes
    (W : SummableModeWeights) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto
      (fun N =>
        cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W)
          (truncateModes N x))
      Filter.atTop
      (nhds (cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W) x)) := by
  exact ((continuous_weightedMode_cutoffPotential W hcutoff).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x))

theorem tendsto_weightedMode_coleHopfPhi_truncateModes
    (W : SummableModeWeights) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto
      (fun N =>
        coleHopfPhi ν
          (cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W))
          (truncateModes N x))
      Filter.atTop
      (nhds (coleHopfPhi ν
        (cutoffPotential cutoff (weightedModeRadius W) (weightedModeStatistic W)) x)) := by
  exact ((continuous_weightedMode_coleHopfPhi W hcutoff).continuousAt.tendsto.comp
    (tendsto_truncateModes_modeState x))

/-- The original geometric weights as an instance of the good observable class. -/
def geometricModeWeights : SummableModeWeights where
  weight := modeWeight
  summable_weight := summable_modeWeight
  weight_nonneg := by
    intro n
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    unfold modeWeight
    exact inv_nonneg.mpr hpow

theorem weightedModeTerm_geometric_eq_modeTerm (x : ModeState) (n : ℕ) :
    weightedModeTerm geometricModeWeights x n = modeTerm x n := by
  simp [weightedModeTerm, geometricModeWeights, modeTerm]

theorem weightedModeRadius_geometric_eq_modeRadius :
    weightedModeRadius geometricModeWeights = modeRadius := by
  funext x
  simp [weightedModeRadius, weightedModeTerm, geometricModeWeights, modeRadius, modeTerm]

theorem weightedModeStatistic_geometric_eq_modeStatistic :
    weightedModeStatistic geometricModeWeights = modeStatistic := by
  funext x
  simp [weightedModeStatistic, modeStatistic, weightedModeRadius_geometric_eq_modeRadius]

end ModeStateObservableClass

end NavierStokes
end FluidDynamics
end Mettapedia
