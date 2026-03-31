import Mettapedia.FluidDynamics.NavierStokes.GeometricModeApproximation

/-!
# Product-Topology Obstruction on the Same Mode State

This file uses the exact `ModeState` and `truncateModes` objects from the
geometric finite-mode approximation model, but equips `ModeState` with the
coordinatewise product topology induced by the coefficient map. In that
topology, truncations converge to the target state. However, a stronger
tail-sensitive observable detecting the presence of any nonzero coefficient is
not continuous, and neither is the associated Cole-Hopf datum.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateProductTopology

instance : TopologicalSpace ModeState :=
  TopologicalSpace.induced ModeState.coeff inferInstance

/-- Zero mode state. -/
def modeZero : ModeState where
  coeff _ := 0
  abs_le_one _ := by simp

/-- A single unit spike pushed out to mode `N`. -/
def tailSpikeMode (N : ℕ) : ModeState where
  coeff n := if n = N then 1 else 0
  abs_le_one n := by
    by_cases h : n = N <;> simp [h]

/-- Stronger tail observable than the geometric radius:
it records whether any nonzero coefficient is present. -/
noncomputable def tailPresenceRadius (x : ModeState) : ℝ :=
  if ∃ n, x.coeff n ≠ 0 then 1 else 0

/-- Constant statistic factor. -/
def unitStatisticMode : ModeState → ℝ := fun _ => 1

theorem tendsto_truncateModes_modeState (x : ModeState) :
    Tendsto (fun N => truncateModes N x) Filter.atTop (nhds x) := by
  rw [nhds_induced]
  simpa [tendsto_iff_comap, Filter.comap_comap, Function.comp] using
    (show Tendsto (fun N : ℕ => (truncateModes N x).coeff) Filter.atTop (nhds x.coeff) from by
      rw [tendsto_pi_nhds]
      intro i
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_gt_atTop i] with N hN
      simp [truncateModes, hN])

theorem tendsto_tailSpikeMode_modeZero :
    Tendsto tailSpikeMode Filter.atTop (nhds modeZero) := by
  rw [nhds_induced]
  simpa [tendsto_iff_comap, Filter.comap_comap, Function.comp] using
    (show Tendsto (fun N : ℕ => (tailSpikeMode N).coeff) Filter.atTop (nhds modeZero.coeff) from by
      rw [tendsto_pi_nhds]
      intro i
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_gt_atTop i] with N hN
      simp [tailSpikeMode, modeZero, Nat.ne_of_lt hN])

theorem tailPresenceRadius_modeZero :
    tailPresenceRadius modeZero = 0 := by
  unfold tailPresenceRadius
  split_ifs with h
  · rcases h with ⟨n, hn⟩
    simp [modeZero] at hn
  · rfl

theorem tailPresenceRadius_tailSpikeMode (N : ℕ) :
    tailPresenceRadius (tailSpikeMode N) = 1 := by
  unfold tailPresenceRadius
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨N, ?_⟩
    simp [tailSpikeMode]

theorem tendsto_tailPresenceRadius_tailSpikeMode :
    Tendsto (fun N => tailPresenceRadius (tailSpikeMode N)) Filter.atTop (nhds (1 : ℝ)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards with N
  simp [tailPresenceRadius_tailSpikeMode]

theorem tendsto_unitStatisticMode_tailSpikeMode :
    Tendsto (fun N => unitStatisticMode (tailSpikeMode N)) Filter.atTop (nhds (1 : ℝ)) := by
  simp [unitStatisticMode]

theorem not_continuousAt_tailPresence_cutoffPotential_modeZero :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) tailPresenceRadius unitStatisticMode) modeZero := by
  refine not_continuousAt_cutoffPotential_of_limit_mismatch
    (u := tailSpikeMode) (x := modeZero) (c := 1) (s := 1)
    tendsto_tailSpikeMode_modeZero ?_ ?_ ?_
  · simpa using tendsto_tailPresenceRadius_tailSpikeMode
  · exact tendsto_unitStatisticMode_tailSpikeMode
  · unfold cutoffPotential
    rw [tailPresenceRadius_modeZero]
    norm_num [unitStatisticMode, modeZero]

theorem not_continuousAt_tailPresence_coleHopfPhi_modeZero :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) tailPresenceRadius unitStatisticMode))
      modeZero := by
  refine not_continuousAt_cutoffColeHopfPhi_of_limit_mismatch
    (u := tailSpikeMode) (x := modeZero) (ν := 1) (c := 1) (s := 1)
    tendsto_tailSpikeMode_modeZero ?_ ?_ (by norm_num) ?_
  · simpa using tendsto_tailPresenceRadius_tailSpikeMode
  · exact tendsto_unitStatisticMode_tailSpikeMode
  · unfold cutoffPotential
    rw [tailPresenceRadius_modeZero]
    norm_num [unitStatisticMode, modeZero]

end ModeStateProductTopology

end NavierStokes
end FluidDynamics
end Mettapedia
