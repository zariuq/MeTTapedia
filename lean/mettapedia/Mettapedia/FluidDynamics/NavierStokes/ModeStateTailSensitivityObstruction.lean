import Mettapedia.FluidDynamics.NavierStokes.ModeStateProductTopologyObstruction

/-!
# Tail-Sensitivity Obstruction on the Shared Mode State

This file packages the generic no-go side of the shared-state fork. If an
observable is constant on the remote single-spike family `tailSpikeMode N` but
takes a different value at `modeZero`, then it is not continuous at `modeZero`.
The same obstruction lifts to cutoff potentials and their Cole-Hopf transforms.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ModeStateTailSensitivityObstruction

/-- `radius` is tail-spike stable at value `r` if every remote single spike has
the same observed radius. -/
def TailSpikeStableAt (radius : ModeState → ℝ) (r : ℝ) : Prop :=
  ∀ N, radius (tailSpikeMode N) = r

theorem tendsto_tailSpikeStableAt {radius : ModeState → ℝ} {r : ℝ}
    (hstable : TailSpikeStableAt radius r) :
    Tendsto (fun N => radius (tailSpikeMode N)) Filter.atTop (nhds r) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards with N
  simp [hstable N]

theorem not_continuousAt_of_tailSpikeStableAt
    {radius : ModeState → ℝ} {r : ℝ}
    (hstable : TailSpikeStableAt radius r)
    (hmismatch : r ≠ radius modeZero) :
    ¬ ContinuousAt radius modeZero := by
  intro hcont
  have htail : Tendsto (fun N => radius (tailSpikeMode N)) Filter.atTop (nhds r) :=
    tendsto_tailSpikeStableAt hstable
  have hzero :
      Tendsto (fun N => radius (tailSpikeMode N)) Filter.atTop (nhds (radius modeZero)) := by
    exact hcont.tendsto.comp tendsto_tailSpikeMode_modeZero
  exact hmismatch (tendsto_nhds_unique htail hzero)

theorem not_continuousAt_cutoffPotential_of_tailSpikeStableAt
    {cutoff : ℝ → ℝ} {radius statistic : ModeState → ℝ}
    {r s : ℝ}
    (hradius : TailSpikeStableAt radius r)
    (hstat :
      Tendsto (fun N => statistic (tailSpikeMode N)) Filter.atTop (nhds s))
    (hmismatch :
      cutoff r * s ≠ cutoffPotential cutoff radius statistic modeZero) :
    ¬ ContinuousAt (cutoffPotential cutoff radius statistic) modeZero := by
  refine not_continuousAt_cutoffPotential_of_limit_mismatch
    (u := tailSpikeMode) (x := modeZero) (c := cutoff r) (s := s)
    tendsto_tailSpikeMode_modeZero ?_ hstat hmismatch
  exact Tendsto.congr' (Eventually.of_forall fun N => by simp [hradius N])
    tendsto_const_nhds

theorem not_continuousAt_coleHopfPhi_of_tailSpikeStableAt
    {ν : ℝ} {cutoff : ℝ → ℝ} {radius statistic : ModeState → ℝ}
    {r s : ℝ}
    (hradius : TailSpikeStableAt radius r)
    (hstat :
      Tendsto (fun N => statistic (tailSpikeMode N)) Filter.atTop (nhds s))
    (hν : ν ≠ 0)
    (hmismatch :
      cutoff r * s ≠ cutoffPotential cutoff radius statistic modeZero) :
    ¬ ContinuousAt
      (coleHopfPhi ν (cutoffPotential cutoff radius statistic))
      modeZero := by
  refine not_continuousAt_cutoffColeHopfPhi_of_limit_mismatch
    (u := tailSpikeMode) (x := modeZero) (ν := ν) (c := cutoff r) (s := s)
    tendsto_tailSpikeMode_modeZero ?_ hstat hν hmismatch
  exact Tendsto.congr' (Eventually.of_forall fun N => by simp [hradius N])
    tendsto_const_nhds

theorem tailPresenceRadius_tailSpikeStableAt_one :
    TailSpikeStableAt tailPresenceRadius 1 := by
  intro N
  exact tailPresenceRadius_tailSpikeMode N

theorem not_continuousAt_tailPresenceRadius_modeZero :
    ¬ ContinuousAt tailPresenceRadius modeZero := by
  exact not_continuousAt_of_tailSpikeStableAt
    tailPresenceRadius_tailSpikeStableAt_one (by simp [tailPresenceRadius_modeZero])

end ModeStateTailSensitivityObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
