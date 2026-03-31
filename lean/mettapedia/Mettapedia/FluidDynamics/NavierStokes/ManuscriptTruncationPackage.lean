import Mettapedia.FluidDynamics.NavierStokes.ApproximationInterface
import Mettapedia.FluidDynamics.NavierStokes.FiniteModeKernelLimit
import Mathlib.Order.Filter.Tendsto

/-!
# Manuscript-Shaped Truncation Package for the NS Grassroots Lane

This file packages the exact combined shape the current grassroots route wants
from the manuscript's finite-mode layer:

- chart observables converge along truncations;
- the induced cutoff potential and Cole-Hopf chart datum converge;
- finite-mode identity data converge with eventual positivity and energy bounds;
- the kernel-founded vorticity bridge is therefore available on the limit data.

The point is not to claim that the SG analytic theorem is done.  The point is
to make its exact Lean target explicit in one place.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ManuscriptTruncationPackage

variable {G Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]
variable {radius statistic : G → ℝ}

/-- Combined manuscript-shaped truncation package:
chart-side cutoff observables plus the finite-mode kernel-founded identity
data needed for the vorticity route. -/
structure ManuscriptTruncationPackage (radius statistic : G → ℝ) extends
    FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X) where
  cutoff : ℝ → ℝ
  cutoff_continuous : Continuous cutoff
  chartApprox : CutoffApproximationData radius statistic

theorem ManuscriptTruncationPackage.cutoffFactor_tendsto
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    Tendsto (fun n => S.cutoff (radius (S.chartApprox.approx n x)))
      Filter.atTop (nhds (S.cutoff (radius x))) := by
  exact S.chartApprox.cutoffFactor_tendsto S.cutoff_continuous x

theorem ManuscriptTruncationPackage.cutoffPotential_tendsto
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    Tendsto (fun n => cutoffPotential S.cutoff radius statistic (S.chartApprox.approx n x))
      Filter.atTop (nhds (cutoffPotential S.cutoff radius statistic x)) := by
  exact S.chartApprox.cutoffPotential_tendsto S.cutoff_continuous x

theorem ManuscriptTruncationPackage.coleHopfPhi_tendsto
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    Tendsto
      (fun n => coleHopfPhi S.ν (cutoffPotential S.cutoff radius statistic) (S.chartApprox.approx n x))
      Filter.atTop
      (nhds (coleHopfPhi S.ν (cutoffPotential S.cutoff radius statistic) x)) := by
  exact S.chartApprox.coleHopfPhi_tendsto S.cutoff_continuous x

theorem ManuscriptTruncationPackage.abs_cutoffPotential_le_of_eventually
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    {M : ℝ} (x : G)
    (hbound :
      ∀ᶠ n in Filter.atTop,
        |cutoffPotential S.cutoff radius statistic (S.chartApprox.approx n x)| ≤ M) :
    |cutoffPotential S.cutoff radius statistic x| ≤ M := by
  exact S.chartApprox.abs_cutoffPotential_le_of_eventually S.cutoff_continuous x hbound

theorem ManuscriptTruncationPackage.abs_coleHopfPhi_le_of_eventually
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    {M : ℝ} (x : G)
    (hbound :
      ∀ᶠ n in Filter.atTop,
        |coleHopfPhi S.ν (cutoffPotential S.cutoff radius statistic) (S.chartApprox.approx n x)| ≤ M) :
    |coleHopfPhi S.ν (cutoffPotential S.cutoff radius statistic) x| ≤ M := by
  exact S.chartApprox.abs_coleHopfPhi_le_of_eventually S.cutoff_continuous x hbound

theorem ManuscriptTruncationPackage.gamma_Wcoeff_le
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (t : Time) :
    gamma (S.toFiniteModeColeHopfKernelData.toColeHopfKernelSemigroupData.Wcoeff t) ≤
      (4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound := by
  simpa using S.toFiniteModeColeHopfKernelData.gamma_Wcoeff_le t

theorem ManuscriptTruncationPackage.abs_vorticity_le
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (t : Time) (x : X) :
    |S.toFiniteModeColeHopfKernelData.toColeHopfKernelSemigroupData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa using S.toFiniteModeColeHopfKernelData.abs_vorticity_le t x

theorem ManuscriptTruncationPackage.abs_vorticity_le_uniform
    (S : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic) :
    ∀ t x, |S.toFiniteModeColeHopfKernelData.toColeHopfKernelSemigroupData.vorticity t x| ≤
      Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound :=
  fun t x => S.abs_vorticity_le t x

end ManuscriptTruncationPackage

end NavierStokes
end FluidDynamics
end Mettapedia
