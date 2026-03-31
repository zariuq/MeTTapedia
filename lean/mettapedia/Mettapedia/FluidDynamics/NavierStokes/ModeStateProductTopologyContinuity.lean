import Mettapedia.FluidDynamics.NavierStokes.ModeStateProductTopologyObstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Product-Topology Continuity on the Same Mode State

This file complements `ModeStateProductTopologyObstruction`. On the exact same
`ModeState` with the exact same coordinatewise product topology, the geometric
radius from `GeometricModeApproximation` is continuous, as are the derived chart
statistic, cutoff potential, and Cole-Hopf datum. This gives a clean Lean split
between a good summable observable and a bad tail-detecting one on one common
state space.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateProductTopologyContinuity

theorem continuous_modeCoeff (n : ℕ) : Continuous fun x : ModeState => x.coeff n := by
  exact (continuous_apply n).comp continuous_induced_dom

theorem continuous_modeTerm (n : ℕ) : Continuous fun x : ModeState => modeTerm x n := by
  simpa [modeTerm] using
    (continuous_abs.comp (continuous_modeCoeff n)).mul (continuous_const : Continuous fun _ : ModeState => modeWeight n)

theorem modeTerm_norm_le_modeWeight (x : ModeState) (n : ℕ) :
    ‖modeTerm x n‖ ≤ modeWeight n := by
  calc
    ‖modeTerm x n‖ = modeTerm x n := by
      simp [modeTerm, modeWeight]
    _ = |x.coeff n| * modeWeight n := rfl
    _ ≤ modeWeight n := by
      have hnonneg : 0 ≤ modeWeight n := by
        have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
        unfold modeWeight
        exact inv_nonneg.mpr hpow
      nlinarith [x.abs_le_one n, hnonneg]

theorem continuous_modeRadius : Continuous modeRadius := by
  unfold modeRadius
  refine continuous_tsum (fun n => continuous_modeTerm n) summable_modeWeight ?_
  intro n x
  exact modeTerm_norm_le_modeWeight x n

theorem continuous_modeStatistic : Continuous modeStatistic := by
  unfold modeStatistic
  exact (continuous_modeCoeff 0).add continuous_modeRadius

theorem continuous_mode_cutoffPotential
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (cutoffPotential cutoff modeRadius modeStatistic) := by
  exact continuous_cutoffPotential hcutoff continuous_modeRadius continuous_modeStatistic

theorem continuous_mode_coleHopfPhi
    {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Continuous (coleHopfPhi ν (cutoffPotential cutoff modeRadius modeStatistic)) := by
  exact continuous_cutoffColeHopfPhi hcutoff continuous_modeRadius continuous_modeStatistic

theorem continuousAt_mode_coleHopfPhi_modeZero
    {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    ContinuousAt
      (coleHopfPhi ν (cutoffPotential cutoff modeRadius modeStatistic))
      modeZero :=
  continuous_mode_coleHopfPhi hcutoff |>.continuousAt

end ModeStateProductTopologyContinuity

end NavierStokes
end FluidDynamics
end Mettapedia
