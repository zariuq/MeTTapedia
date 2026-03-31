import Mettapedia.FluidDynamics.NavierStokes.ApproximationInterface
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric Finite-Mode Approximation Model for the NS Grassroots Lane

This file instantiates the abstract approximation interface with a simple
infinite-mode model. A state is a bounded real coefficient sequence. The chart
radius is a geometrically weighted tail-sensitive observable, and truncation at
level `N` keeps only the first `N` modes. Lean proves that the weighted radius,
the derived chart statistic, the cutoff potential, and the induced Cole-Hopf
datum all converge along these finite-mode truncations.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section GeometricModeApproximation

/-- Bounded coefficient sequences, normalized so each mode has magnitude at most `1`. -/
structure ModeState where
  coeff : ℕ → ℝ
  abs_le_one : ∀ n, |coeff n| ≤ 1

/-- Geometric mode weight. -/
noncomputable def modeWeight (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- Weighted contribution of the `n`-th mode to the chart radius. -/
noncomputable def modeTerm (x : ModeState) (n : ℕ) : ℝ := |x.coeff n| * modeWeight n

/-- Weighted chart radius on the infinite mode state. -/
noncomputable def modeRadius (x : ModeState) : ℝ := ∑' n, modeTerm x n

/-- A simple chart statistic: visible zeroth mode plus the weighted radius. -/
noncomputable def modeStatistic (x : ModeState) : ℝ := x.coeff 0 + modeRadius x

/-- Finite-mode truncation: keep only modes below `N`. -/
def truncateModes (N : ℕ) (x : ModeState) : ModeState where
  coeff n := if n < N then x.coeff n else 0
  abs_le_one n := by
    by_cases h : n < N
    · simpa [h] using x.abs_le_one n
    · simp [h]

theorem summable_modeWeight : Summable modeWeight := by
  convert
    (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ))
      (by norm_num : |(1 / 2 : ℝ)| < 1))
    using 1
  ext n
  simp [modeWeight]

theorem summable_modeTerm (x : ModeState) : Summable (modeTerm x) := by
  refine Summable.of_norm_bounded summable_modeWeight ?_
  intro n
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

theorem modeTerm_truncate_eq (x : ModeState) {N n : ℕ} (hn : n < N) :
    modeTerm (truncateModes N x) n = modeTerm x n := by
  simp [modeTerm, truncateModes, hn]

theorem modeTerm_truncate_eq_zero (x : ModeState) {N n : ℕ} (hn : N ≤ n) :
    modeTerm (truncateModes N x) n = 0 := by
  simp [modeTerm, truncateModes, not_lt.mpr hn]

theorem modeRadius_truncate_eq_sum (x : ModeState) (N : ℕ) :
    modeRadius (truncateModes N x) = Finset.sum (Finset.range N) (fun n => modeTerm x n) := by
  rw [modeRadius, tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    exact modeTerm_truncate_eq x (Finset.mem_range.mp hn)
  · intro n hn
    exact modeTerm_truncate_eq_zero x (not_lt.mp (by simpa using hn))

theorem truncateModes_radius_tendsto (x : ModeState) :
    Tendsto (fun N => modeRadius (truncateModes N x))
      Filter.atTop (nhds (modeRadius x)) := by
  convert (summable_modeTerm x).hasSum.tendsto_sum_nat using 1
  ext N
  exact modeRadius_truncate_eq_sum x N

theorem truncateModes_zeroMode_tendsto (x : ModeState) :
    Tendsto (fun N => (truncateModes N x).coeff 0)
      Filter.atTop (nhds (x.coeff 0)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  simp [truncateModes, hN]

theorem truncateModes_statistic_tendsto (x : ModeState) :
    Tendsto (fun N => modeStatistic (truncateModes N x))
      Filter.atTop (nhds (modeStatistic x)) := by
  unfold modeStatistic
  simpa using (truncateModes_zeroMode_tendsto x).add (truncateModes_radius_tendsto x)

/-- Concrete finite-mode approximation package feeding the generic interface. -/
noncomputable def modeApproximationData : CutoffApproximationData modeRadius modeStatistic where
  approx := truncateModes
  radius_tendsto := truncateModes_radius_tendsto
  statistic_tendsto := truncateModes_statistic_tendsto

theorem modeApproximation_cutoffPotential_tendsto
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N =>
      cutoffPotential cutoff modeRadius modeStatistic
        (modeApproximationData.approx N x))
      Filter.atTop
      (nhds (cutoffPotential cutoff modeRadius modeStatistic x)) := by
  exact modeApproximationData.cutoffPotential_tendsto hcutoff x

theorem modeApproximation_coleHopfPhi_tendsto
    {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N =>
      coleHopfPhi ν (cutoffPotential cutoff modeRadius modeStatistic)
        (modeApproximationData.approx N x))
      Filter.atTop
      (nhds (coleHopfPhi ν (cutoffPotential cutoff modeRadius modeStatistic) x)) := by
  exact modeApproximationData.coleHopfPhi_tendsto hcutoff x

end GeometricModeApproximation

end NavierStokes
end FluidDynamics
end Mettapedia
