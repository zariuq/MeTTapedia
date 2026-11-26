import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstructionCore
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelBridgeDichotomy

/-!
# Anchored Shift-Invariant Top-Down Bridge Obstruction

This module contains the corresponding exactness and obstruction surfaces for top-down bridges over anchored spatial-shift kernels.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
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
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν curlFrame curlBound curlBound_nonneg hcurl x
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat B hCand hnz₁ hnz₂

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
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
  have hsumK :
      SeedLiveShiftKernel.totalCoeffSum
          (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) ≠ 0 := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hsum
  have hstrict :=
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν curlFrame curlBound curlBound_nonneg hcurl x
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

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
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
  intro hB
  rcases hB with ⟨B, hCand⟩
  have hstrict :=
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz
  exact (not_lt_of_ge hlarge) hstrict

theorem WeightedObservable.not_exists_windowedColeHopfHeatAnchoredShiftTopDownBridge_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
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
  intro hB
  rcases hB with ⟨B, hCand⟩
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat B hCand hnz₁ hnz₂
  exact habs hEq


end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
