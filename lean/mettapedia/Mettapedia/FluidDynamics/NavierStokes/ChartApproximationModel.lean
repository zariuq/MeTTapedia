import Mettapedia.FluidDynamics.NavierStokes.ApproximationInterface

/-!
# Concrete Chart/Truncation Model for the NS Grassroots Lane

This file instantiates the abstract approximation interface with a small
two-coordinate chart model. The first coordinate is a visible component and the
second is a hidden chart statistic. The truncation drops the hidden component
at stage `0` and is exact thereafter, so the approximation theorems can be used
without any analytic overhead.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ChartApproximationModel

/-- Toy chart state with one visible and one hidden coordinate. -/
abbrev ChartState := ℝ × ℝ

/-- Radius observable carried by the hidden coordinate. -/
def chartRadius : ChartState → ℝ := Prod.snd

/-- A simple chart statistic mixing visible and hidden data. -/
def chartStatistic : ChartState → ℝ := fun x => x.1 + x.2

/-- Toy finite-mode approximation:
stage `0` drops the hidden coordinate, all later stages are exact. -/
def truncateHidden (n : ℕ) (x : ChartState) : ChartState :=
  if n = 0 then (x.1, 0) else x

theorem truncateHidden_radius_tendsto (x : ChartState) :
    Tendsto (fun n => chartRadius (truncateHidden n x))
      Filter.atTop (nhds (chartRadius x)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp [truncateHidden, chartRadius, Nat.ne_of_gt hn]

theorem truncateHidden_statistic_tendsto (x : ChartState) :
    Tendsto (fun n => chartStatistic (truncateHidden n x))
      Filter.atTop (nhds (chartStatistic x)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp [truncateHidden, chartStatistic, Nat.ne_of_gt hn]

/-- The concrete approximation package feeding the generic interface. -/
def chartApproximationData :
    CutoffApproximationData chartRadius chartStatistic where
  approx := truncateHidden
  radius_tendsto := truncateHidden_radius_tendsto
  statistic_tendsto := truncateHidden_statistic_tendsto

theorem chartApproximation_cutoffPotential_tendsto
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ChartState) :
    Tendsto (fun n =>
      cutoffPotential cutoff chartRadius chartStatistic
        (chartApproximationData.approx n x))
      Filter.atTop
      (nhds (cutoffPotential cutoff chartRadius chartStatistic x)) := by
  exact chartApproximationData.cutoffPotential_tendsto hcutoff x

theorem chartApproximation_coleHopfPhi_tendsto
    {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ChartState) :
    Tendsto (fun n =>
      coleHopfPhi ν (cutoffPotential cutoff chartRadius chartStatistic)
        (chartApproximationData.approx n x))
      Filter.atTop
      (nhds (coleHopfPhi ν (cutoffPotential cutoff chartRadius chartStatistic) x)) := by
  exact chartApproximationData.coleHopfPhi_tendsto hcutoff x

end ChartApproximationModel

end NavierStokes
end FluidDynamics
end Mettapedia
