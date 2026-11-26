import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatAnchoredShiftKernelFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelCandidateBounds

/-!
# Anchored Shift-Invariant Saturated Candidate Obstruction

This module contains the exactness and obstruction surfaces for anchored spatial-shift candidates under stationarity and shift invariance.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

variable {ι X : Type*}
variable [Fintype ι] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
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
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  let coeffSum := baseCoeff + seedCoeff + shiftCoeff
  have hEqPoint (t : NNReal) (y : X) :
      satCoeff * (T.vorticity t y / (1 + |T.vorticity t y|)) = coeffSum * T.vorticity t y := by
    calc
      satCoeff * (T.vorticity t y / (1 + |T.vorticity t y|))
          = (L.windowedColeHopfHeatSaturatedCandidate
              (ι := ι) (X := X)
              selector satCoeff c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                rfl
      _ = (L.windowedColeHopfHeatAnchoredShiftCandidate
              (ι := ι) (X := X)
              selector s baseCoeff seedCoeff shiftCoeff c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                exact congrFun (congrFun (congrArg VelocityPressureCandidate.velocity hCand.symm) t) y
      _ = coeffSum * T.vorticity t y := by
            simp [coeffSum, T, WeightedObservable.windowedColeHopfHeatAnchoredShiftCandidate,
              UniformVorticityTendril.seedLiveOperatorCandidate, anchoredSeedLiveBlendOperator,
              hshiftInv t y, hstat t (y + s), add_assoc, add_left_comm, add_comm, add_mul]
  have hCoeffFormula (t : NNReal) (y : X) (hnz : T.vorticity t y ≠ 0) :
      coeffSum * (1 + |T.vorticity t y|) = satCoeff := by
    let w := T.vorticity t y
    have hw : satCoeff * (w / (1 + |w|)) = coeffSum * w := by
      simpa [w] using hEqPoint t y
    have hden : (1 + |w|) ≠ 0 := by positivity
    have hmul : satCoeff * w = (coeffSum * (1 + |w|)) * w := by
      calc
        satCoeff * w = (satCoeff * (w / (1 + |w|))) * (1 + |w|) := by
          field_simp [hden]
        _ = (coeffSum * w) * (1 + |w|) := by
          rw [hw]
        _ = (coeffSum * (1 + |w|)) * w := by
          ring
    have hzero : (satCoeff - coeffSum * (1 + |w|)) * w = 0 := by
      nlinarith [hmul]
    rcases mul_eq_zero.mp hzero with hfac | hwzero
    · linarith
    · exact False.elim (hnz hwzero)
  have h1 : coeffSum * (1 + |T.vorticity t₁ y₁|) = satCoeff :=
    hCoeffFormula t₁ y₁ hnz₁
  have h2 : coeffSum * (1 + |T.vorticity t₂ y₂|) = satCoeff :=
    hCoeffFormula t₂ y₂ hnz₂
  have hdiff :
      coeffSum *
        (|T.vorticity t₁ y₁| - |T.vorticity t₂ y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hdiff with hsum0 | habs
  · exact False.elim (hsum (by simpa [coeffSum] using hsum0))
  · linarith

theorem WeightedObservable.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
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
        selector satCoeff c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
    rw [L.windowedColeHopfHeatAnchoredTranslationShiftKernelCandidate_eq_anchoredShiftCandidate
      (ι := ι) (X := X)
      (selector := selector) (s := s) (a := baseCoeff) (b := seedCoeff) (d := shiftCoeff)
      (c := c) (ν := ν) (hc := hc) (hν := hν) (curlFrame := curlFrame)
      (curlBound := curlBound) (curlBound_nonneg := curlBound_nonneg)
      (hcurl := hcurl) (x := x)]
    exact hCand
  have hstrict :=
    L.windowedColeHopfHeatShiftKernel_abs_totalCoeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_totalCoeffSum_ne_zero_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector (anchoredTranslationShiftKernel (X := X) s baseCoeff seedCoeff shiftCoeff)
      satCoeff c ν hsumK hc hν curlFrame curlBound curlBound_nonneg hcurl x
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      (by
        intro i t y
        fin_cases i <;> simp [anchoredTranslationShiftKernel, hshiftInv t y])
      hstat hCandK hnz
  simpa [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
    SeedLiveShiftKernel.liveCoeffSum, anchoredTranslationShiftKernel,
    Finset.sum_add_distrib, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
    using hstrict

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_saturatedCoeff_le_abs_coeffSum_of_stationary_shiftInvariant
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
  intro hCand
  have hstrict :=
    L.windowedColeHopfHeatAnchoredShift_abs_coeffSum_lt_abs_saturatedCoeff_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz
  exact (not_lt_of_ge hlarge) hstrict

theorem WeightedObservable.not_windowedColeHopfHeatAnchoredShiftCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
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
    L.windowedColeHopfHeatAnchoredShift_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector s baseCoeff seedCoeff shiftCoeff satCoeff c ν hsum hc hν
      curlFrame curlBound curlBound_nonneg hcurl x hshiftInv hstat hCand hnz₁ hnz₂
  exact habs hEq


end WindowedColeHopfHeatSaturatedAnchoredShiftInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
