import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelIdentitySampleSpecialization
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

/-!
# Saturated Frontier for Identity-Anchor Sample Kernels

This file specializes the constructive saturated shift-kernel corridor to the
finite sampled-kernel family whose seed and live anchors are both the identity.

If the total seed/live coefficient mass is `a / (1 + r)` and the concrete
windowed vorticity tendril has constant absolute magnitude `r`, then the
sampled route already realizes the nonlinear saturated initial slice.  Under
the additional stationarity hypothesis between the seeded slice and the live
slice, the sampled-kernel candidate itself coincides with the nonlinear
saturated candidate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  have hInitEq :=
    L.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum K.identityShiftKernel = a / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, SeedLiveSampleKernel.identityShiftKernel,
      SeedLiveSampleKernel.seedCoeffSum, SeedLiveSampleKernel.liveCoeffSum,
      add_assoc, add_left_comm, add_comm] using hcoeff
  have hShiftEq :=
    L.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K.identityShiftKernel a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      habs
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice, hInitEq] using hShiftEq

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatSampleKernelInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hInitEq :=
    L.windowedColeHopfHeatSampleKernelInitialSlice_eq_shiftKernelInitialSlice_of_identityAnchors_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hK
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum K.identityShiftKernel = a / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, SeedLiveSampleKernel.identityShiftKernel,
      SeedLiveSampleKernel.seedCoeffSum, SeedLiveSampleKernel.liveCoeffSum,
      add_assoc, add_left_comm, add_comm] using hcoeff
  have hShiftEq :=
    L.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K.identityShiftKernel a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      habs
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le, hInitEq] using hShiftEq

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  have hCandEq :=
    L.windowedColeHopfHeatSampleKernelCandidate_eq_shiftKernelCandidate_of_identityAnchors
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x hK
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum K.identityShiftKernel = a / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, SeedLiveSampleKernel.identityShiftKernel,
      SeedLiveSampleKernel.seedCoeffSum, SeedLiveSampleKernel.liveCoeffSum,
      add_assoc, add_left_comm, add_comm] using hcoeff
  have hShiftEq :=
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K.identityShiftKernel a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      hstat habs
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedCandidate, hCandEq] using hShiftEq

theorem WeightedObservable.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
      selector K c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hCandEq :=
    L.windowedColeHopfHeatSampleKernelCandidate_eq_shiftKernelCandidate_of_identityAnchors_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hK
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum K.identityShiftKernel = a / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, SeedLiveSampleKernel.identityShiftKernel,
      SeedLiveSampleKernel.seedCoeffSum, SeedLiveSampleKernel.liveCoeffSum,
      add_assoc, add_left_comm, add_comm] using hcoeff
  have hShiftEq :=
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K.identityShiftKernel a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      (by
        intro i t y
        simp [SeedLiveSampleKernel.identityShiftKernel, add_zero])
      hstat habs
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le, hCandEq] using hShiftEq

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_identitySampleKernel_of_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
  simpa [L.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude
      (ι := ι) (X := X)
      (selector := selector) (K := K) (a := a) (r := r) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
      (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)
      hK hcoeff habs]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_identitySampleKernel_of_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
  simpa [L.windowedColeHopfHeatIdentitySampleKernelInitialSlice_eq_saturatedInitialSlice_of_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      (selector := selector) (K := K) (a := a) (r := r) (c := c) (ν := ν)
      (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlComponentBound := curlComponentBound)
      (hcurlComponentBound_nonneg := hcurlComponentBound_nonneg) (hcurl := hcurl) (x := x)
      hK hcoeff habs]
    using
      (L.windowedColeHopfHeat_realizes_sampleKernel_pressure_seeded_clause_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector K c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatSampleKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hK hcoeff hstat habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedIdentitySampleKernelBridge_of_stationary_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveSampleKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hK : K.IdentityAnchors)
    (hcoeff : K.liveCoeffSum + K.seedCoeffSum = a / (1 + r))
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
              selector K c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (sampleKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatSampleKernelBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector K c ν hc hν
    curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatIdentitySampleKernelCandidate_eq_saturatedCandidate_of_stationary_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hK hcoeff hstat habs

end WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
