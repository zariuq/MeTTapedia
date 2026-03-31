import Mettapedia.FluidDynamics.NavierStokes.ColeHopfTopology

/-!
# Product-Topology `ℓ¹` Countermodel for the NS Grassroots Lane

This file formalizes a cleaner infinite-mode topology mismatch. The ambient
state space is the raw sequence space `ℕ → ℝ` with the product topology. Finite
mode truncations converge coordinatewise in that topology, but the stronger
tail-sensitive observable `∑' n, |x n|` is not continuous there. The induced
Cole-Hopf datum is therefore not continuous either.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ProductTopologyL1Countermodel

/-- Raw infinite-mode state space with the product topology. -/
abbrev SequenceState := ℕ → ℝ

/-- Finite-mode truncation keeping only coordinates below `N`. -/
def truncateSequence (N : ℕ) (x : SequenceState) : SequenceState :=
  fun n => if n < N then x n else 0

/-- Zero sequence. -/
def zeroSequence : SequenceState := fun _ => 0

/-- Tail spike moving out to higher and higher coordinates. -/
def tailSpike (N : ℕ) : SequenceState := fun n => if n = N then 1 else 0

/-- Tail-sensitive `ℓ¹` observable. -/
noncomputable def l1Radius (x : SequenceState) : ℝ := ∑' n, |x n|

/-- Constant statistic factor. -/
def unitStatistic : SequenceState → ℝ := fun _ => 1

theorem tendsto_truncateSequence (x : SequenceState) :
    Tendsto (fun N => truncateSequence N x) Filter.atTop (nhds x) := by
  rw [tendsto_pi_nhds]
  intro i
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop i] with N hN
  simp [truncateSequence, hN]

theorem tendsto_tailSpike_zeroSequence :
    Tendsto tailSpike Filter.atTop (nhds zeroSequence) := by
  rw [tendsto_pi_nhds]
  intro i
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop i] with N hN
  simp [tailSpike, zeroSequence, Nat.ne_of_lt hN]

theorem l1Radius_zeroSequence :
    l1Radius zeroSequence = 0 := by
  simp [l1Radius, zeroSequence]

theorem l1Radius_tailSpike (N : ℕ) :
    l1Radius (tailSpike N) = 1 := by
  rw [l1Radius, tsum_eq_single N]
  · simp [tailSpike]
  · intro n hn
    simp [tailSpike, hn]

theorem tendsto_l1Radius_tailSpike :
    Tendsto (fun N => l1Radius (tailSpike N)) Filter.atTop (nhds (1 : ℝ)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards with N
  simp [l1Radius_tailSpike]

theorem tendsto_unitStatistic_tailSpike :
    Tendsto (fun N => unitStatistic (tailSpike N)) Filter.atTop (nhds (1 : ℝ)) := by
  simp [unitStatistic]

theorem not_continuousAt_l1_cutoffPotential_zeroSequence :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) l1Radius unitStatistic) zeroSequence := by
  refine not_continuousAt_cutoffPotential_of_limit_mismatch
    (u := tailSpike) (x := zeroSequence) (c := 1) (s := 1)
    tendsto_tailSpike_zeroSequence ?_ ?_ ?_
  · simpa using tendsto_l1Radius_tailSpike
  · exact tendsto_unitStatistic_tailSpike
  · norm_num [cutoffPotential, l1Radius_zeroSequence, unitStatistic, zeroSequence]

theorem not_continuousAt_l1_coleHopfPhi_zeroSequence :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) l1Radius unitStatistic))
      zeroSequence := by
  refine not_continuousAt_cutoffColeHopfPhi_of_limit_mismatch
    (u := tailSpike) (x := zeroSequence) (ν := 1) (c := 1) (s := 1)
    tendsto_tailSpike_zeroSequence ?_ ?_ (by norm_num) ?_
  · simpa using tendsto_l1Radius_tailSpike
  · exact tendsto_unitStatistic_tailSpike
  · norm_num [cutoffPotential, l1Radius_zeroSequence, unitStatistic, zeroSequence]

end ProductTopologyL1Countermodel

end NavierStokes
end FluidDynamics
end Mettapedia
