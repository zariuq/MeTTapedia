import Mettapedia.FluidDynamics.NavierStokes.GeometricColeHopfSharedApproximation
import Mathlib.Order.Filter.Tendsto

/-!
# Concrete Package for the Geometric Cole-Hopf Shared Instance

This file turns the Cole-Hopf-shaped shared approximation instance into named
concrete objects and direct consequence theorems.  The goal is to expose the
package-level bounds without making readers chase the whole abstraction stack.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter

section GeometricColeHopfPackage

variable {Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]

/-- The explicit lower bound carried by the geometric Cole-Hopf shared model. -/
def WeightedObservable.geometricColeHopfLowerBound
    (L : WeightedObservable) (ν B : ℝ) : ℝ :=
  Real.exp (-(B * observableEnvelopeSum L) / (2 * ν))

/-- The explicit coefficient-energy bound carried by the geometric Cole-Hopf
shared model. -/
def WeightedObservable.geometricColeHopfEnergyBound
    (L : WeightedObservable) (ν B : ℝ) : ℝ :=
  (Real.exp ((B * observableEnvelopeSum L) / (2 * ν))) ^ 2 * (Fintype.card ι : ℝ)

/-- The concrete manuscript-shaped truncation package coming from the geometric
Cole-Hopf shared instance. -/
def WeightedObservable.geometricColeHopfManuscriptPackage
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X)
      radiusSq (matchingObservable L) := by
  let S : SharedApproximationPackage (Time := Time) (ι := ι) (X := X)
      radiusSq (matchingObservable L) :=
    L.geometricColeHopfSharedApproximation
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl
  exact S.toManuscriptTruncationPackage x cutoff hcutoff_cont

/-- The concrete finite-mode kernel data extracted from the packaged geometric
Cole-Hopf shared instance. -/
def WeightedObservable.geometricColeHopfFiniteModeKernelData
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    FiniteModeColeHopfKernelData (Time := Time) (ι := ι) (X := X) :=
  (L.geometricColeHopfManuscriptPackage
    selector ν B hν hB cutoff hcutoff_cont hcutoff
    curlFrame curlBound curlBound_nonneg hcurl x).toFiniteModeColeHopfKernelData

/-- The concrete Cole-Hopf kernel semigroup data extracted from the packaged
geometric shared instance. -/
def WeightedObservable.geometricColeHopfKernelSemigroupData
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ColeHopfKernelSemigroupData (Time := Time) (ι := ι) (X := X) :=
  (L.geometricColeHopfFiniteModeKernelData
    selector ν B hν hB cutoff hcutoff_cont hcutoff
    curlFrame curlBound curlBound_nonneg hcurl x).toColeHopfKernelSemigroupData

/-- Named concrete vorticity field coming from the packaged Cole-Hopf shared
instance. -/
def WeightedObservable.geometricColeHopfVorticity
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) : Time → X → ℝ :=
  (L.geometricColeHopfKernelSemigroupData
    selector ν B hν hB cutoff hcutoff_cont hcutoff
    curlFrame curlBound curlBound_nonneg hcurl x).vorticity

theorem WeightedObservable.geometricColeHopfPackage_cutoffPotential_tendsto
    (L : WeightedObservable)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (x : ModeState) :
    Tendsto
      (fun n => cutoffPotential cutoff radiusSq (matchingObservable L) (truncateModes n x))
      Filter.atTop
      (nhds (cutoffPotential cutoff radiusSq (matchingObservable L) x)) := by
  exact (manuscriptApproximationData L).cutoffPotential_tendsto hcutoff_cont x

theorem WeightedObservable.geometricColeHopfPackage_coleHopfPhi_tendsto
    (L : WeightedObservable)
    (ν : ℝ)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (x : ModeState) :
    Tendsto
      (fun n => coleHopfPhi ν (cutoffPotential cutoff radiusSq (matchingObservable L)) (truncateModes n x))
      Filter.atTop
      (nhds (coleHopfPhi ν (cutoffPotential cutoff radiusSq (matchingObservable L)) x)) := by
  exact (manuscriptApproximationData L).coleHopfPhi_tendsto hcutoff_cont x

theorem WeightedObservable.geometricColeHopfPackage_gamma_Wcoeff_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) (t : Time) :
    gamma
      ((L.geometricColeHopfKernelSemigroupData
        (Time := Time) (ι := ι) (X := X)
        selector ν B hν hB cutoff hcutoff_cont hcutoff
        curlFrame curlBound curlBound_nonneg hcurl x).Wcoeff t) ≤
      (4 * ν ^ 2 / (L.geometricColeHopfLowerBound ν B) ^ 2) *
        L.geometricColeHopfEnergyBound (ι := ι) ν B := by
  let P :=
    (L.geometricColeHopfManuscriptPackage
      (Time := Time) (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl x
      : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X)
          radiusSq (matchingObservable L))
  simpa [WeightedObservable.geometricColeHopfFiniteModeKernelData,
    WeightedObservable.geometricColeHopfKernelSemigroupData,
    WeightedObservable.geometricColeHopfLowerBound,
    WeightedObservable.geometricColeHopfEnergyBound,
    WeightedObservable.geometricColeHopfManuscriptPackage, P] using P.gamma_Wcoeff_le t

theorem WeightedObservable.geometricColeHopfPackage_abs_vorticity_le_uniform
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (ν B : ℝ)
    (hν : 0 < ν)
    (hB : 0 ≤ B)
    (cutoff : ℝ → ℝ)
    (hcutoff_cont : Continuous cutoff)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) :
    ∀ t : Time, ∀ y : X, |L.geometricColeHopfVorticity
      (Time := Time) (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl x t y| ≤
      Real.sqrt
        ((4 * ν ^ 2 / (L.geometricColeHopfLowerBound ν B) ^ 2) *
          L.geometricColeHopfEnergyBound (ι := ι) ν B) *
        Real.sqrt curlBound := by
  let P :=
    (L.geometricColeHopfManuscriptPackage
      (Time := Time) (ι := ι) (X := X)
      selector ν B hν hB cutoff hcutoff_cont hcutoff curlFrame curlBound curlBound_nonneg hcurl x
      : ManuscriptTruncationPackage (Time := Time) (ι := ι) (X := X)
          radiusSq (matchingObservable L))
  simpa [WeightedObservable.geometricColeHopfVorticity,
    WeightedObservable.geometricColeHopfFiniteModeKernelData,
    WeightedObservable.geometricColeHopfKernelSemigroupData,
    WeightedObservable.geometricColeHopfLowerBound,
    WeightedObservable.geometricColeHopfEnergyBound,
    WeightedObservable.geometricColeHopfManuscriptPackage, P] using P.abs_vorticity_le_uniform

end GeometricColeHopfPackage

end NavierStokes
end FluidDynamics
end Mettapedia
