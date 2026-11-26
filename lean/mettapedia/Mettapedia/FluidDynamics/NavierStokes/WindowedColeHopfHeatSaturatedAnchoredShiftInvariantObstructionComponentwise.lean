import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionBridge
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelBridgeComponentwise

/-!
# Anchored Shift-Invariant Componentwise-Bound Obstruction

This module lifts the anchored candidate and top-down bridge obstruction surfaces to componentwise curl-bound inputs.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| =
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂| := by
  exact
      (L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hshiftInv hstat hCand hnz₁ hnz₂)

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hCand :
      L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  simpa [WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le,
      WeightedObservable.windowedColeHopfHeatSharedPackage_of_componentwise_abs_le,
      WeightedObservable.geometricColeHopfHeatApproximation_of_componentwise_abs_le]
    using
      (L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hshiftInv hstat hCand hnz)

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  intro hCand
  have hstrict :=
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hshiftInv hstat hCand hnz
  exact (not_lt_of_ge hlarge) hstrict

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂|) :
    L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  intro hCand
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hshiftInv hstat hCand
      hnz₁ hnz₂
  exact habs hEq

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| =
    |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂| := by
  have hsumK :
      SeedLiveShiftKernel.totalCoeffSum
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) ≠ 0 := by
    intro hzero
    exact hsum (by
      simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
        SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
        Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
        using hzero)
  exact
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat B hCand hnz₁ hnz₂

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (B :
      TopDownFeffermanBridge
        (pressureSeededPredicateKit
          (Time := NNReal) (X := X)
          (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
            c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
        (shiftKernelCompatibilityPred
          (Time := NNReal) (X := X)
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
    (hCand :
      B.candidate =
        L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    |baseCoeff + seedCoeff + shiftCoeff| < |satCoeff| := by
  have hsumK :
      SeedLiveShiftKernel.totalCoeffSum
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) ≠ 0 := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hsum
  have hstrict :=
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat B hCand hnz
  simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
    SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
    Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
    using hstrict

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hlarge : |satCoeff| ≤ |baseCoeff + seedCoeff + shiftCoeff|)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    {t : NNReal} {y : X}
    (hnz :
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y ≠ 0) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  have hstrict :=
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hshiftInv hstat B hCand hnz
  exact (not_lt_of_ge hlarge) hstrict

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff c ν : ℝ)
    (hsum : baseCoeff + seedCoeff + shiftCoeff ≠ 0)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t
          (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hwitness :
      ∃ t₁ t₂ y₁ y₂,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0 ∧
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0 ∧
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₁ y₁| ≠
          |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t₂ y₂|) :
    ¬ ∃ B :
        TopDownFeffermanBridge
          (pressureSeededPredicateKit
            (Time := NNReal) (X := X)
            (L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
              (ι := ι) (X := X)
              selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
              c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X)
            (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector satCoeff c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x hshiftInv hstat B hCand
      hnz₁ hnz₂
  exact habs hEq


end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
