import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionCore
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionBridge
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedIdentitySampleKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedDiagonalSampleKernelFrontier

/-!
# Anchored, masked, identity, and diagonal saturated-kernel regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression


section WindowedColeHopfHeatSaturatedAnchoredShiftInvariant

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem windowed_heat_saturated_anchored_shiftInvariant_candidate_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem windowed_heat_saturated_anchored_shiftInvariant_candidate_abs_coeffSum_lt_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_candidate_of_abs_saturatedCoeff_le_abs_coeffSum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hlarge hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_clause_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_anchoredShift_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hcoeff hshiftInv habs

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
            (L.windowedColeHopfHeatShiftKernelInitialSlice
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν
            curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.exists_windowedColeHopfHeatSaturatedAnchoredShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_abs_eq_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
    |(L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz₁ hnz₂

theorem windowed_heat_saturated_anchored_shiftInvariant_bridge_abs_coeffSum_lt_abs_saturatedCoeff_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  exact
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_bridge_of_abs_saturatedCoeff_le_abs_coeffSum_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hlarge hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hnz

theorem windowed_heat_saturated_anchored_shiftInvariant_no_bridge_of_abs_ne_abs_regression
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y)
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
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hwitness

end WindowedColeHopfHeatSaturatedAnchoredShiftInvariant
end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia
