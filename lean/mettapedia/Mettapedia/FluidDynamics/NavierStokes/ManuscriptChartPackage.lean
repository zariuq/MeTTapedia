import Mettapedia.FluidDynamics.NavierStokes.ManuscriptChartDatum
import Mettapedia.FluidDynamics.NavierStokes.ManuscriptTruncationPackage
import Mathlib.Order.Filter.Tendsto

/-!
# Concrete Packaging of the Manuscript Chart Datum

This file plugs the concrete D.4-style chart model into the already-existing
combined truncation package.  The chart side is no longer only abstract:
any kernel-founded finite-mode identity package can now be paired with the
concrete `radiusSq` / `matchingObservable` chart data immediately.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section ManuscriptChartPackage

variable {Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]

/-- The concrete D.4-style chart model feeds directly into the combined
manuscript-shaped truncation package. -/
def WeightedObservable.toManuscriptTruncationPackage
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    (cutoff : ℝ → ℝ) (hcutoff : Continuous cutoff) :
    ManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X)
      radiusSq (matchingObservable L) where
  toFiniteModeColeHopfKernelData := S
  cutoff := cutoff
  cutoff_continuous := hcutoff
  chartApprox := manuscriptApproximationData L

theorem WeightedObservable.package_cutoffPotential_tendsto
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto
      (fun N =>
        cutoffPotential cutoff radiusSq (matchingObservable L) (truncateModes N x))
      Filter.atTop
      (nhds (cutoffPotential cutoff radiusSq (matchingObservable L) x)) := by
  simpa [WeightedObservable.toManuscriptTruncationPackage] using
    (WeightedObservable.toManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X) L S cutoff hcutoff).cutoffPotential_tendsto x

theorem WeightedObservable.package_coleHopfPhi_tendsto
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto
      (fun N =>
        coleHopfPhi S.ν (cutoffPotential cutoff radiusSq (matchingObservable L))
          (truncateModes N x))
      Filter.atTop
      (nhds (coleHopfPhi S.ν (cutoffPotential cutoff radiusSq (matchingObservable L)) x)) := by
  simpa [WeightedObservable.toManuscriptTruncationPackage] using
    (WeightedObservable.toManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X) L S cutoff hcutoff).coleHopfPhi_tendsto x

theorem WeightedObservable.package_abs_vorticity_le_uniform
    (L : WeightedObservable)
    (S : FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X))
    {cutoff : ℝ → ℝ} (hcutoff : Continuous cutoff) :
    ∀ t x,
      |(S.toColeHopfKernelSemigroupData.vorticity t x)| ≤
        Real.sqrt ((4 * S.ν ^ 2 / S.mPhi ^ 2) * S.energyBound) * Real.sqrt S.curlBound := by
  simpa [WeightedObservable.toManuscriptTruncationPackage] using
    (WeightedObservable.toManuscriptTruncationPackage
      (Time := Time) (ι := ι) (X := X) L S cutoff hcutoff).abs_vorticity_le_uniform

end ManuscriptChartPackage

end NavierStokes
end FluidDynamics
end Mettapedia
