import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatAnchoredShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

/-!
# Anchored Spatial Invariant Frontier for the Saturated Route

This file specializes the full invariant saturated shift-kernel corridor to the
first concrete spatial anchored blend route.

Under stationarity, invariance under the spatial shift `x ↦ x + s`, and
constant absolute magnitude `r`, the anchored blend

`baseCoeff * ω(t, x) + seedCoeff * ω(1, x + s) + shiftCoeff * ω(t, x + s)`

realizes the nonlinear saturated descendant whenever the total coefficient mass
is `satCoeff / (1 + r)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
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
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  have hshiftK :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
    exact
      L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
        satCoeff r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
        hcoeffK
        (by
          intro i t y
          fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
        (by
          intro i t y
          fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
        hstat habs
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := baseCoeff) (b := seedCoeff) (d := shiftCoeff)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using hshiftK

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_anchoredShift_of_shiftInvariant_constantMagnitude
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
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedAnchoredShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
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
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  exact
    L.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat habs

theorem WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatAnchoredShiftCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  have hshiftK :
      L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
        c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
    exact
      L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
        satCoeff r c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
        hcoeffK
        (by
          intro i t y
          fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
        (by
          intro i t y
          fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
        hstat habs
  simpa [L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := baseCoeff) (b := seedCoeff) (d := shiftCoeff)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlComponentBound := curlComponentBound)
      (hcurlComponentBound_nonneg := hcurlComponentBound_nonneg)
      (hcurl := hcurl) (x := x)]
    using hshiftK

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_anchoredShift_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    FeffermanGlobalRegularityClause
      (pressureSeededPredicateKit
        (Time := NNReal) (X := X)
        (L.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector satCoeff c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) := by
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedAnchoredShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (s : X)
    (baseCoeff seedCoeff shiftCoeff satCoeff r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : baseCoeff + seedCoeff + shiftCoeff = satCoeff / (1 + r))
    (hshiftInv :
      ∀ t : NNReal, ∀ y : X,
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t (y + s) =
        (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    ∃ B :
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
            selector satCoeff c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  have hcoeffK :
      SeedLiveShiftKernel.totalCoeffSum
        (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff) =
        satCoeff / (1 + r) := by
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hcoeff
  exact
    L.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeffK
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat habs

end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
