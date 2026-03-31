import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Tendsto

/-!
# Cutoff Continuity Interface for the NS Grassroots Lane

This file isolates the generic continuity mechanism behind the chart-cutoff
datum discussed in the NS crux note.  The target is not the full SG geometry;
it is the small reusable fact pattern:

- if the radius map and statistic are continuous, then the cutoff potential is
  continuous;
- if a sequence converges in the ambient topology but the cutoff factor tends to
  the wrong limit, then the cutoff potential cannot be continuous there.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section Basic

variable {G : Type*}

/-- Generic cutoff-shaped potential:
apply a scalar cutoff to a radius observable and multiply by a statistic. -/
def cutoffPotential (cutoff : ℝ → ℝ) (radius statistic : G → ℝ) : G → ℝ :=
  fun x => cutoff (radius x) * statistic x

/-- Sequential obstruction:
if the cutoff factor tends to `c`, the statistic tends to `s`, and the product
limit does not match the claimed value at `x`, then the cutoff potential cannot
converge to its value at `x`. -/
theorem not_tendsto_cutoffPotential_of_limit_mismatch
    {u : ℕ → G} {x : G}
    {cutoff : ℝ → ℝ} {radius statistic : G → ℝ}
    {c s : ℝ}
    (hcut : Tendsto (fun n => cutoff (radius (u n))) Filter.atTop (nhds c))
    (hstat : Tendsto (fun n => statistic (u n)) Filter.atTop (nhds s))
    (hmismatch : c * s ≠ cutoffPotential cutoff radius statistic x) :
    ¬ Tendsto (fun n => cutoffPotential cutoff radius statistic (u n))
        Filter.atTop (nhds (cutoffPotential cutoff radius statistic x)) := by
  intro hW
  have hprod :
      Tendsto (fun n => cutoffPotential cutoff radius statistic (u n))
        Filter.atTop (nhds (c * s)) := by
    simpa [cutoffPotential] using hcut.mul hstat
  have heq :
      c * s = cutoffPotential cutoff radius statistic x :=
    tendsto_nhds_unique hprod hW
  exact hmismatch heq

end Basic

section Topology

variable {G : Type*} [TopologicalSpace G]

/-- If both scalar observables are continuous, then the induced cutoff potential
is continuous. -/
theorem continuous_cutoffPotential
    {cutoff : ℝ → ℝ} {radius statistic : G → ℝ}
    (hcutoff : Continuous cutoff)
    (hradius : Continuous radius)
    (hstat : Continuous statistic) :
    Continuous (cutoffPotential cutoff radius statistic) := by
  unfold cutoffPotential
  exact (hcutoff.comp hradius).mul hstat

/-- Pointwise version of `continuous_cutoffPotential`. -/
theorem continuousAt_cutoffPotential
    {cutoff : ℝ → ℝ} {radius statistic : G → ℝ} {x : G}
    (hcutoff : ContinuousAt cutoff (radius x))
    (hradius : ContinuousAt radius x)
    (hstat : ContinuousAt statistic x) :
    ContinuousAt (cutoffPotential cutoff radius statistic) x := by
  unfold cutoffPotential
  exact (hcutoff.comp hradius).mul hstat

/-- Continuity obstruction packaged at the point `x`. -/
theorem not_continuousAt_cutoffPotential_of_limit_mismatch
    {u : ℕ → G} {x : G}
    {cutoff : ℝ → ℝ} {radius statistic : G → ℝ}
    {c s : ℝ}
    (hu : Tendsto u Filter.atTop (nhds x))
    (hcut : Tendsto (fun n => cutoff (radius (u n))) Filter.atTop (nhds c))
    (hstat : Tendsto (fun n => statistic (u n)) Filter.atTop (nhds s))
    (hmismatch : c * s ≠ cutoffPotential cutoff radius statistic x) :
    ¬ ContinuousAt (cutoffPotential cutoff radius statistic) x := by
  intro hcont
  exact not_tendsto_cutoffPotential_of_limit_mismatch
    (x := x) (cutoff := cutoff) (radius := radius) (statistic := statistic)
    hcut hstat hmismatch (hcont.tendsto.comp hu)

end Topology

end NavierStokes
end FluidDynamics
end Mettapedia
