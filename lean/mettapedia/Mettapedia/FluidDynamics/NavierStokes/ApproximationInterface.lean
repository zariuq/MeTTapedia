import Mettapedia.FluidDynamics.NavierStokes.ColeHopfTopology

/-!
# Approximation Interface for the NS Grassroots Lane

This file packages the positive repair obligation suggested by the NS crux
analysis.  If a future truncation / approximation theorem shows that the chart
radius observable and the chart statistic both converge along approximants, then
the cutoff potential and its Cole-Hopf transform converge automatically.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ApproximationInterface

variable {G : Type*}
variable {radius statistic : G → ℝ}

/-- Abstract approximation package for the chart radius and statistic.

`approx n x` should be thought of as an `n`-th truncation or finite-mode
approximation to `x`.  The structure records only the convergence facts the
cutoff/Cole-Hopf layer actually needs. -/
structure CutoffApproximationData (radius statistic : G → ℝ) where
  approx : ℕ → G → G
  radius_tendsto :
    ∀ x, Tendsto (fun n => radius (approx n x)) Filter.atTop (nhds (radius x))
  statistic_tendsto :
    ∀ x, Tendsto (fun n => statistic (approx n x)) Filter.atTop (nhds (statistic x))

theorem abs_le_of_tendsto_of_eventually_abs_le
    {u : ℕ → ℝ} {c M : ℝ}
    (hu : Tendsto u Filter.atTop (nhds c))
    (hbound : ∀ᶠ n in Filter.atTop, |u n| ≤ M) :
    |c| ≤ M := by
  have hmem : ∀ᶠ n in Filter.atTop, u n ∈ Set.Icc (-M) M := by
    filter_upwards [hbound] with n hn
    simpa [Set.mem_Icc, abs_le] using hn
  have hc : c ∈ Set.Icc (-M) M := isClosed_Icc.mem_of_tendsto hu hmem
  simpa [Set.mem_Icc, abs_le] using hc

theorem CutoffApproximationData.cutoffFactor_tendsto
    (A : CutoffApproximationData radius statistic)
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : G) :
    Tendsto (fun n => cutoff (radius (A.approx n x)))
      Filter.atTop (nhds (cutoff (radius x))) := by
  exact hcutoff.continuousAt.tendsto.comp (A.radius_tendsto x)

theorem CutoffApproximationData.cutoffPotential_tendsto
    (A : CutoffApproximationData radius statistic)
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : G) :
    Tendsto (fun n => cutoffPotential cutoff radius statistic (A.approx n x))
      Filter.atTop (nhds (cutoffPotential cutoff radius statistic x)) := by
  have hcut := A.cutoffFactor_tendsto hcutoff x
  have hstat := A.statistic_tendsto x
  simpa [cutoffPotential] using hcut.mul hstat

theorem CutoffApproximationData.coleHopfPhi_tendsto
    (A : CutoffApproximationData radius statistic)
    {ν : ℝ} {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : G) :
    Tendsto (fun n => coleHopfPhi ν (cutoffPotential cutoff radius statistic) (A.approx n x))
      Filter.atTop
      (nhds (coleHopfPhi ν (cutoffPotential cutoff radius statistic) x)) := by
  exact ((continuous_coleHopfScalar ν).continuousAt.tendsto.comp
    (A.cutoffPotential_tendsto hcutoff x))

theorem CutoffApproximationData.abs_cutoffPotential_le_of_eventually
    (A : CutoffApproximationData radius statistic)
    {cutoff : ℝ → ℝ} {M : ℝ} (hcutoff : Continuous cutoff) (x : G)
    (hbound :
      ∀ᶠ n in Filter.atTop,
        |cutoffPotential cutoff radius statistic (A.approx n x)| ≤ M) :
    |cutoffPotential cutoff radius statistic x| ≤ M := by
  exact abs_le_of_tendsto_of_eventually_abs_le
    (A.cutoffPotential_tendsto hcutoff x) hbound

theorem CutoffApproximationData.abs_cutoffPotential_le_of_forall
    (A : CutoffApproximationData radius statistic)
    {cutoff : ℝ → ℝ} {M : ℝ} (hcutoff : Continuous cutoff) (x : G)
    (hbound :
      ∀ n, |cutoffPotential cutoff radius statistic (A.approx n x)| ≤ M) :
    |cutoffPotential cutoff radius statistic x| ≤ M := by
  exact A.abs_cutoffPotential_le_of_eventually hcutoff x (Eventually.of_forall hbound)

theorem CutoffApproximationData.abs_coleHopfPhi_le_of_eventually
    (A : CutoffApproximationData radius statistic)
    {ν : ℝ} {cutoff : ℝ → ℝ} {M : ℝ} (hcutoff : Continuous cutoff) (x : G)
    (hbound :
      ∀ᶠ n in Filter.atTop,
        |coleHopfPhi ν (cutoffPotential cutoff radius statistic) (A.approx n x)| ≤ M) :
    |coleHopfPhi ν (cutoffPotential cutoff radius statistic) x| ≤ M := by
  exact abs_le_of_tendsto_of_eventually_abs_le
    (A.coleHopfPhi_tendsto hcutoff x) hbound

theorem CutoffApproximationData.abs_coleHopfPhi_le_of_forall
    (A : CutoffApproximationData radius statistic)
    {ν : ℝ} {cutoff : ℝ → ℝ} {M : ℝ} (hcutoff : Continuous cutoff) (x : G)
    (hbound :
      ∀ n, |coleHopfPhi ν (cutoffPotential cutoff radius statistic) (A.approx n x)| ≤ M) :
    |coleHopfPhi ν (cutoffPotential cutoff radius statistic) x| ≤ M := by
  exact A.abs_coleHopfPhi_le_of_eventually hcutoff x (Eventually.of_forall hbound)

end ApproximationInterface

end NavierStokes
end FluidDynamics
end Mettapedia
