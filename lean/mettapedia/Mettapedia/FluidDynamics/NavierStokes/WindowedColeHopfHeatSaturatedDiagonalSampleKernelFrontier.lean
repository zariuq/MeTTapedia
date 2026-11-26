import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSampleKernelFrontier

/-!
# Saturated Frontier for the Diagonal One-Sample Kernel

This file exposes the constructive nonlinear saturated corridor directly on the
older diagonal one-sample shell.  Since the diagonal sampled kernel keeps both
seed and live anchors equal to the identity, it is just the one-point instance
of the identity-anchor sampled family.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontier

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeffK habs

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hK hcoeffK habs

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelCandidate
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeffK hstat habs

theorem WeightedObservable.windowedColeHopfHeatDiagonalSampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hK hcoeffK hstat habs

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_diagonalSampleKernel_of_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_identitySampleKernel_of_constantMagnitude
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeffK habs

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_diagonalSampleKernel_of_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_identitySampleKernel_of_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hK hcoeffK habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedDiagonalSampleKernelBridge_of_stationary_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice
              (ι := ι) (X := X)
              selector (diagonalSampleKernel (X := X) p q) c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (diagonalSampleKernel (X := X) p q))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeffK hstat habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedDiagonalSampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (p q a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : p + q = a / (1 + r))
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector (diagonalSampleKernel (X := X) p q) c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (diagonalSampleKernel (X := X) p q))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hK : (diagonalSampleKernel (X := X) p q).IdentityAnchors := by
    constructor <;> intro i y <;> simp [diagonalSampleKernel]
  have hcoeffK :
      (diagonalSampleKernel (X := X) p q).liveCoeffSum +
          (diagonalSampleKernel (X := X) p q).seedCoeffSum =
        a / (1 + r) := by
    simpa [SeedLiveSampleKernel.liveCoeffSum, SeedLiveSampleKernel.seedCoeffSum,
      diagonalSampleKernel, add_comm] using hcoeff
  exact
    L.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (diagonalSampleKernel (X := X) p q) a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hK hcoeffK hstat habs

end WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
