import Mettapedia.FluidDynamics.NavierStokes.ContinuationRegressionWindowedSaturatedInvariantBridgePart1

/-!
# Saturated shift-kernel invariant bridge regression checks

Top-down bridge regressions for the windowed saturated shift-kernel invariant
route, separated from the candidate-only surface.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression


section WindowedColeHopfHeatSaturatedShiftKernelInvariant

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]
theorem windowed_heat_saturated_shiftKernel_invariant_bridge_abs_sum_le_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| ≤ |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_le_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_bridge_abs_sum_lt_abs_saturatedCoeff_of_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice
            (ι := ι) (X := X)
            selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |SeedLiveShiftKernel.totalCoeffSum K| < |a| := by
  exact
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_saturatedCoeff_lt_abs_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| < |SeedLiveShiftKernel.totalCoeffSum K|)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_lt_abs_totalCoeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_saturatedCoeff_le_abs_sum_nonzero_sum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hlarge : |a| ≤ |SeedLiveShiftKernel.totalCoeffSum K|)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_totalCoeffSum_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hlarge hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hnz

theorem windowed_heat_saturated_shiftKernel_invariant_no_bridge_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum : SeedLiveShiftKernel.totalCoeffSum K ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hwitness
end WindowedColeHopfHeatSaturatedShiftKernelInvariant
end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
