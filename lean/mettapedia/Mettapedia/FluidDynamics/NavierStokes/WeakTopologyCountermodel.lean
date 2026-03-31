import Mettapedia.FluidDynamics.NavierStokes.ColeHopfTopology
import Mathlib.Topology.Order

/-!
# Weak Topology Countermodel for the NS Grassroots Lane

This file instantiates the abstract cutoff/Cole-Hopf interface with a concrete
topological countermodel. The ambient topology only sees the first coordinate,
while the cutoff datum depends on the second coordinate. This yields explicit
non-continuity of both the cutoff potential and its Cole-Hopf transform.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section WeakTopology

/-- A toy state space with the topology induced by the first coordinate only. -/
abbrev WeakState := ℝ × ℝ

instance : TopologicalSpace WeakState :=
  TopologicalSpace.induced Prod.fst inferInstance

/-- The distinguished base point. -/
def weakOrigin : WeakState := (0, 0)

/-- A constant sequence invisible to the weak topology but changing the hidden coordinate. -/
def hiddenTail : ℕ → WeakState := fun _ => (0, 1)

/-- The weak topology only sees the first coordinate, so `hiddenTail` tends to `weakOrigin`. -/
theorem tendsto_hiddenTail_weakOrigin :
    Tendsto hiddenTail Filter.atTop (nhds weakOrigin) := by
  rw [nhds_induced, tendsto_iff_comap]
  have hconst : Filter.atTop ≤ Filter.comap (fun _ : ℕ => (0 : ℝ)) (nhds 0) := by
    simpa [tendsto_iff_comap] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  have hcomp : Filter.atTop ≤ Filter.comap (Prod.fst ∘ hiddenTail) (nhds 0) := by
    simpa [hiddenTail, Function.comp] using hconst
  simpa [Filter.comap_comap, Function.comp] using hcomp

/-- Radius observable carried by the hidden coordinate. -/
def hiddenRadius : WeakState → ℝ := Prod.snd

/-- Constant statistic factor. -/
def constantStatistic : WeakState → ℝ := fun _ => 1

/-- Along the hidden-tail sequence, the radius stays equal to `1`. -/
theorem tendsto_hiddenRadius_hiddenTail :
    Tendsto (fun n => hiddenRadius (hiddenTail n)) Filter.atTop (nhds (1 : ℝ)) := by
  simp [hiddenRadius, hiddenTail]

/-- Along the hidden-tail sequence, the statistic stays equal to `1`. -/
theorem tendsto_constantStatistic_hiddenTail :
    Tendsto (fun n => constantStatistic (hiddenTail n)) Filter.atTop (nhds (1 : ℝ)) := by
  simp [constantStatistic]

/-- With cutoff `id`, the induced cutoff potential is not continuous at the origin. -/
theorem not_continuousAt_hidden_cutoffPotential :
    ¬ ContinuousAt
      (cutoffPotential (fun r => r) hiddenRadius constantStatistic) weakOrigin := by
  refine not_continuousAt_cutoffPotential_of_limit_mismatch
    (u := hiddenTail) (x := weakOrigin) (c := 1) (s := 1)
    tendsto_hiddenTail_weakOrigin
    ?_ ?_ ?_
  · exact tendsto_hiddenRadius_hiddenTail
  · exact tendsto_constantStatistic_hiddenTail
  · norm_num [cutoffPotential, weakOrigin, hiddenRadius, constantStatistic]

/-- The same hidden-coordinate mismatch also breaks the Cole-Hopf transform. -/
theorem not_continuousAt_hidden_coleHopfPhi :
    ¬ ContinuousAt
      (coleHopfPhi 1 (cutoffPotential (fun r => r) hiddenRadius constantStatistic))
      weakOrigin := by
  refine not_continuousAt_cutoffColeHopfPhi_of_limit_mismatch
    (u := hiddenTail) (x := weakOrigin) (ν := 1) (c := 1) (s := 1)
    tendsto_hiddenTail_weakOrigin
    ?_ ?_ (by norm_num) ?_
  · exact tendsto_hiddenRadius_hiddenTail
  · exact tendsto_constantStatistic_hiddenTail
  · norm_num [cutoffPotential, weakOrigin, hiddenRadius, constantStatistic]

end WeakTopology

end NavierStokes
end FluidDynamics
end Mettapedia
