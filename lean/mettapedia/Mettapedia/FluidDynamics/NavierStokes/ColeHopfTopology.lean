import Mettapedia.FluidDynamics.NavierStokes.CutoffContinuity
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Topological Cole-Hopf Shell for the NS Grassroots Lane

This file packages the purely topological `W ↦ φ` step of the SG-Cole-Hopf
route.  It isolates what the analytic route must supply if one wants the actual
chart-cutoff datum to behave well in the chosen topology.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section Basic

variable {G : Type*}

/-- The scalar Cole-Hopf transform applied to a real potential value. -/
def coleHopfScalar (ν : ℝ) : ℝ → ℝ :=
  fun y => Real.exp (-y / (2 * ν))

/-- The corresponding field-level Cole-Hopf transform. -/
def coleHopfPhi (ν : ℝ) (W : G → ℝ) : G → ℝ :=
  fun x => coleHopfScalar ν (W x)

theorem continuous_coleHopfScalar (ν : ℝ) :
    Continuous (coleHopfScalar ν) := by
  simpa [coleHopfScalar] using
    Real.continuous_exp.comp (continuous_id.neg.div_const (2 * ν))

theorem injective_coleHopfScalar {ν : ℝ} (hν : ν ≠ 0) :
    Function.Injective (coleHopfScalar ν) := by
  intro a b hab
  have h2ν : 2 * ν ≠ 0 := by
    exact mul_ne_zero (by norm_num) hν
  have hlin : -a / (2 * ν) = -b / (2 * ν) := Real.exp_injective hab
  have hneg : -a = -b := (div_left_inj' h2ν).mp hlin
  exact neg_injective hneg

theorem coleHopfScalar_ne_of_ne {ν a b : ℝ}
    (hν : ν ≠ 0) (hab : a ≠ b) :
    coleHopfScalar ν a ≠ coleHopfScalar ν b := by
  intro h
  exact hab (injective_coleHopfScalar hν h)

theorem not_tendsto_coleHopfPhi_of_limit_mismatch
    {u : ℕ → G} {x : G} {ν c : ℝ} {W : G → ℝ}
    (hW : Tendsto (fun n => W (u n)) Filter.atTop (nhds c))
    (hmismatch : coleHopfScalar ν c ≠ coleHopfPhi ν W x) :
    ¬ Tendsto (fun n => coleHopfPhi ν W (u n))
        Filter.atTop (nhds (coleHopfPhi ν W x)) := by
  intro hphi
  have hphi' :
      Tendsto (fun n => coleHopfPhi ν W (u n))
        Filter.atTop (nhds (coleHopfScalar ν c)) := by
    exact ((continuous_coleHopfScalar ν).continuousAt.tendsto.comp hW)
  have heq : coleHopfScalar ν c = coleHopfPhi ν W x :=
    tendsto_nhds_unique hphi' hphi
  exact hmismatch heq

theorem not_tendsto_coleHopfPhi_of_potential_mismatch
    {u : ℕ → G} {x : G} {ν c : ℝ} {W : G → ℝ}
    (hW : Tendsto (fun n => W (u n)) Filter.atTop (nhds c))
    (hν : ν ≠ 0)
    (hmismatch : c ≠ W x) :
    ¬ Tendsto (fun n => coleHopfPhi ν W (u n))
        Filter.atTop (nhds (coleHopfPhi ν W x)) := by
  apply not_tendsto_coleHopfPhi_of_limit_mismatch (x := x) (ν := ν) (c := c) hW
  exact coleHopfScalar_ne_of_ne hν hmismatch

end Basic

section Topology

variable {G : Type*} [TopologicalSpace G]

theorem continuous_coleHopfPhi {ν : ℝ} {W : G → ℝ}
    (hW : Continuous W) :
    Continuous (coleHopfPhi ν W) :=
  continuous_coleHopfScalar ν |>.comp hW

theorem continuousAt_coleHopfPhi {ν : ℝ} {W : G → ℝ} {x : G}
    (hW : ContinuousAt W x) :
    ContinuousAt (coleHopfPhi ν W) x :=
  (continuous_coleHopfScalar ν).continuousAt.comp hW

theorem not_continuousAt_coleHopfPhi_of_potential_mismatch
    {u : ℕ → G} {x : G} {ν c : ℝ} {W : G → ℝ}
    (hu : Tendsto u Filter.atTop (nhds x))
    (hW : Tendsto (fun n => W (u n)) Filter.atTop (nhds c))
    (hν : ν ≠ 0)
    (hmismatch : c ≠ W x) :
    ¬ ContinuousAt (coleHopfPhi ν W) x := by
  intro hcont
  exact not_tendsto_coleHopfPhi_of_potential_mismatch
    (x := x) (ν := ν) (c := c) (W := W) hW hν hmismatch
    (hcont.tendsto.comp hu)

theorem continuous_cutoffColeHopfPhi
    {ν : ℝ} {cutoff : ℝ → ℝ} {radius statistic : G → ℝ}
    (hcutoff : Continuous cutoff)
    (hradius : Continuous radius)
    (hstat : Continuous statistic) :
    Continuous (coleHopfPhi ν (cutoffPotential cutoff radius statistic)) :=
  continuous_coleHopfPhi
    (continuous_cutoffPotential hcutoff hradius hstat)

theorem not_continuousAt_cutoffColeHopfPhi_of_limit_mismatch
    {u : ℕ → G} {x : G}
    {ν c s : ℝ}
    {cutoff : ℝ → ℝ} {radius statistic : G → ℝ}
    (hu : Tendsto u Filter.atTop (nhds x))
    (hcut : Tendsto (fun n => cutoff (radius (u n))) Filter.atTop (nhds c))
    (hstat : Tendsto (fun n => statistic (u n)) Filter.atTop (nhds s))
    (hν : ν ≠ 0)
    (hmismatch : c * s ≠ cutoffPotential cutoff radius statistic x) :
    ¬ ContinuousAt (coleHopfPhi ν (cutoffPotential cutoff radius statistic)) x := by
  intro hcont
  have hW :
      Tendsto (fun n => cutoffPotential cutoff radius statistic (u n))
        Filter.atTop (nhds (c * s)) := by
    simpa [cutoffPotential] using hcut.mul hstat
  exact not_tendsto_coleHopfPhi_of_potential_mismatch
    (x := x) (ν := ν) (c := c * s)
    (W := cutoffPotential cutoff radius statistic)
    hW hν hmismatch (hcont.tendsto.comp hu)

end Topology

end NavierStokes
end FluidDynamics
end Mettapedia
