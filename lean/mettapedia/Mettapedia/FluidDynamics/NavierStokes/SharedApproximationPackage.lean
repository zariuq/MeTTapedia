import Mettapedia.FluidDynamics.NavierStokes.ApproximationInterface
import Mettapedia.FluidDynamics.NavierStokes.FiniteModeKernelLimit
import Mettapedia.FluidDynamics.NavierStokes.ManuscriptTruncationPackage

/-!
# Shared Approximation Package for the NS Grassroots Lane

This file unifies the chart-side and identity-energy-side approximation data.
Instead of keeping two merely compatible approximation stories, it records one
common finite-mode family `approx : ℕ → G → G` and derives both packages from
that same object.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section SharedApproximationPackage

variable {G Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]
variable {radius statistic : G → ℝ}

/-- One shared approximation family feeding both the chart-cutoff observables
and the identity-only Cole-Hopf data. -/
structure SharedApproximationPackage (radius statistic : G → ℝ) extends
    KernelSemigroupData (Time := Time) where
  approx : ℕ → G → G
  radius_tendsto :
    ∀ x, Tendsto (fun n => radius (approx n x)) Filter.atTop (nhds (radius x))
  statistic_tendsto :
    ∀ x, Tendsto (fun n => statistic (approx n x)) Filter.atTop (nhds (statistic x))
  Phi : G → Time → ℝ
  dPhi : G → Time → ι → ℝ
  ν : ℝ
  mPhi : ℝ
  energyBound : ℝ
  curlFrame : ι → X → ℝ
  curlBound : ℝ
  mPhi_pos : 0 < mPhi
  energyBound_nonneg : 0 ≤ energyBound
  curlBound_nonneg : 0 ≤ curlBound
  Phi_tendsto :
    ∀ x t, Tendsto (fun n => Phi (approx n x) t) Filter.atTop (nhds (Phi x t))
  dPhi_tendsto :
    ∀ x t i, Tendsto (fun n => dPhi (approx n x) t i) Filter.atTop (nhds (dPhi x t i))
  Phi_lower_eventually :
    ∀ x t, ∀ᶠ n in Filter.atTop, mPhi ≤ Phi (approx n x) t
  dPhi_energy_eventually :
    ∀ x t, ∀ᶠ n in Filter.atTop, gamma (fun i => dPhi (approx n x) t i) ≤ energyBound
  curl_energy :
    ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound

/-- The shared approximation family immediately yields the chart-side
approximation interface. -/
def SharedApproximationPackage.toCutoffApproximationData
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic) :
    CutoffApproximationData radius statistic where
  approx := S.approx
  radius_tendsto := S.radius_tendsto
  statistic_tendsto := S.statistic_tendsto

/-- The same approximation family also yields finite-mode identity data at each
base state. -/
def SharedApproximationPackage.toFiniteModeColeHopfData
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FiniteModeColeHopfData (Time := Time) (ι := ι) (X := X) where
  Phi := S.Phi x
  dPhi := S.dPhi x
  approxPhi := fun n t => S.Phi (S.approx n x) t
  approxdPhi := fun n t i => S.dPhi (S.approx n x) t i
  ν := S.ν
  mPhi := S.mPhi
  energyBound := S.energyBound
  curlFrame := S.curlFrame
  curlBound := S.curlBound
  mPhi_pos := S.mPhi_pos
  energyBound_nonneg := S.energyBound_nonneg
  curlBound_nonneg := S.curlBound_nonneg
  Phi_tendsto := S.Phi_tendsto x
  dPhi_tendsto := S.dPhi_tendsto x
  Phi_lower_eventually := S.Phi_lower_eventually x
  dPhi_energy_eventually := S.dPhi_energy_eventually x
  curl_energy := S.curl_energy

/-- Adding the local kernel shell to the shared package yields the existing
kernel-founded finite-mode interface. -/
def SharedApproximationPackage.toFiniteModeColeHopfKernelData
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) :
    FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X) where
  toKernelSemigroupData := S.toKernelSemigroupData
  toFiniteModeColeHopfData := S.toFiniteModeColeHopfData x

/-- The single shared approximation object now lands directly in the combined
manuscript-shaped truncation package. -/
def SharedApproximationPackage.toManuscriptTruncationPackage
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) (cutoff : ℝ → ℝ) (hcutoff : Continuous cutoff) :
    ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X) radius statistic where
  toFiniteModeColeHopfKernelData := S.toFiniteModeColeHopfKernelData x
  cutoff := cutoff
  cutoff_continuous := hcutoff
  chartApprox := S.toCutoffApproximationData

theorem SharedApproximationPackage.cutoffPotential_tendsto
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Tendsto
      (fun n => cutoffPotential cutoff radius statistic (S.approx n x))
      Filter.atTop
      (nhds (cutoffPotential cutoff radius statistic x)) := by
  simpa [SharedApproximationPackage.toCutoffApproximationData] using
    (S.toCutoffApproximationData.cutoffPotential_tendsto hcutoff x)

theorem SharedApproximationPackage.coleHopfPhi_tendsto
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    Tendsto
      (fun n => coleHopfPhi S.ν (cutoffPotential cutoff radius statistic) (S.approx n x))
      Filter.atTop
      (nhds (coleHopfPhi S.ν (cutoffPotential cutoff radius statistic) x)) := by
  simpa [SharedApproximationPackage.toManuscriptTruncationPackage] using
    (S.toManuscriptTruncationPackage x cutoff hcutoff).coleHopfPhi_tendsto x

theorem SharedApproximationPackage.abs_vorticity_le_uniform
    (S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X) radius statistic)
    (x : G) {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    ∀ t y,
      |(S.toFiniteModeColeHopfKernelData x).toColeHopfKernelSemigroupData.vorticity t y| ≤
        Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa [SharedApproximationPackage.toManuscriptTruncationPackage] using
    (S.toManuscriptTruncationPackage x cutoff hcutoff).abs_vorticity_le_uniform

end SharedApproximationPackage

end NavierStokes
end FluidDynamics
end Mettapedia
