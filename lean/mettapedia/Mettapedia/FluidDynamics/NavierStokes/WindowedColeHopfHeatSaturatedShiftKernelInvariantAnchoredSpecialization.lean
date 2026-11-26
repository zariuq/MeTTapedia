import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelCandidateDichotomy
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedAnchoredShiftInvariantFrontier

/-!
# Anchored Specialization of the Invariant Saturated Shift-Kernel Exactness Theorem

This file shows that the concrete anchored spatial exactness theorem is a
special case of the newer full invariant finite shift-kernel exactness theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelInvariantAnchoredSpecialization

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_via_shiftKernelInvariant
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
    simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
      SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
      Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      using hsum
  have hCandK :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
        c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector satCoeff c ν hc hν
        curlFrame curlBound curlBound_nonneg hcurl x := by
    rw [L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := baseCoeff) (b := seedCoeff) (d := shiftCoeff)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    exact hCand
  exact
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν curlFrame curlBound curlBound_nonneg hcurl x
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat hCandK hnz₁ hnz₂

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_via_shiftKernelInvariant
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
    L.windowedColeHopfHeatAnchoredShiftCandidate
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector satCoeff c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hCand
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_via_shiftKernelInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz₁ hnz₂
  exact habs hEq

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_via_shiftKernelInvariant_of_componentwise_abs_le
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
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t (y + s) =
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
      (L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant_via_shiftKernelInvariant
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hshiftInv hstat hCand hnz₁ hnz₂)

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_via_shiftKernelInvariant_of_componentwise_abs_le
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
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t (y + s) =
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
  exact
      (L.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant_via_shiftKernelInvariant
        (ι := ι) (X := X)
        selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
        curlFrame ((Fintype.card ι : ℝ) * curlComponentBound ^ 2) (by positivity)
        (fun x => gamma_le_card_mul_sq_of_abs_le
          (D := fun i => curlFrame i x) hcurlComponentBound_nonneg (hcurl x))
        x hshiftInv hstat hwitness)

end WindowedColeHopfHeatSaturatedShiftKernelInvariantAnchoredSpecialization

end NavierStokes
end FluidDynamics
end Mettapedia
