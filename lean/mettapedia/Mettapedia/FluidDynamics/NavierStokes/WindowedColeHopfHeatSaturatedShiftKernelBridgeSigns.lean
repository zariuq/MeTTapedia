import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelCandidateDichotomy

/-!
# Windowed Cole-Hopf Saturated Shift-Kernel: BridgeSigns

Top-down bridge coefficient identity and sign obstructions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_totalCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
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
    SeedLiveShiftKernel.totalCoeffSum K *
        (1 + |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y|) =
      a := by
  have hcompat :
      shiftKernelCompatibilityPred (Time := NNReal) (X := X) K
        (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
        (L.windowedColeHopfHeatSaturatedCandidate
          (ι := ι) (X := X)
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).velocity := by
    simpa [hCand] using B.compatibility.vorticity_generated_by_velocity
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  have hEqPoint :
      a * (T.vorticity t y / (1 + |T.vorticity t y|)) =
        SeedLiveShiftKernel.totalCoeffSum K * T.vorticity t y := by
    calc
      a * (T.vorticity t y / (1 + |T.vorticity t y|))
          = (L.windowedColeHopfHeatSaturatedCandidate
              (ι := ι) (X := X)
              selector a c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                rfl
      _ = (L.windowedColeHopfHeatShiftKernelCandidate
              (ι := ι) (X := X)
              selector K c ν hc hν
              curlFrame curlBound curlBound_nonneg hcurl x).velocity t y := by
                exact hcompat t y
      _ = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
            K.liveCoeff i * T.vorticity t (y + K.liveShift i)) := by
            simp [WeightedObservable.windowedColeHopfHeatShiftKernelCandidate,
              UniformVorticityTendril.seedLiveOperatorCandidate,
              SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator, T]
      _ = ∑ i, (K.seedCoeff i + K.liveCoeff i) * T.vorticity t y := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hseedInv i 1 y, hstat t y, hliveInv i t y]
            ring
      _ = (∑ i, (K.seedCoeff i + K.liveCoeff i)) * T.vorticity t y := by
            simpa using
              (Finset.sum_mul
                (s := Finset.univ)
                (f := fun i : κ => K.seedCoeff i + K.liveCoeff i)
                (a := T.vorticity t y)).symm
      _ = SeedLiveShiftKernel.totalCoeffSum K * T.vorticity t y := by
            simp [SeedLiveShiftKernel.totalCoeffSum, SeedLiveShiftKernel.seedCoeffSum,
              SeedLiveShiftKernel.liveCoeffSum, Finset.sum_add_distrib, add_mul]
  let w := T.vorticity t y
  have hw :
      a * (w / (1 + |w|)) = SeedLiveShiftKernel.totalCoeffSum K * w := by
    simpa [w] using hEqPoint
  have hden : (1 + |w|) ≠ 0 := by positivity
  have hmul :
      a * w = (SeedLiveShiftKernel.totalCoeffSum K * (1 + |w|)) * w := by
    calc
      a * w = (a * (w / (1 + |w|))) * (1 + |w|) := by
        field_simp [hden]
      _ = (SeedLiveShiftKernel.totalCoeffSum K * w) * (1 + |w|) := by
        rw [hw]
      _ = (SeedLiveShiftKernel.totalCoeffSum K * (1 + |w|)) * w := by
        ring
  have hzero :
      (a - SeedLiveShiftKernel.totalCoeffSum K * (1 + |w|)) * w = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hzero with hfac | hwzero
  · simpa [T, w] using (by linarith : SeedLiveShiftKernel.totalCoeffSum K * (1 + |w|) = a)
  · exact False.elim (hnz (by simpa [T, w] using hwzero))

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_totalCoeffSum_pos_of_saturatedCoeff_pos_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (ha : 0 < a)
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
    0 < SeedLiveShiftKernel.totalCoeffSum K := by
  have hcoeff :=
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz
  have hfactor :
      0 <
        1 + |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| := by
    positivity
  nlinarith [hcoeff, hfactor, ha]

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_totalCoeffSum_neg_of_saturatedCoeff_neg_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (ha : a < 0)
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
    SeedLiveShiftKernel.totalCoeffSum K < 0 := by
  have hcoeff :=
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_mul_one_add_abs_eq_saturatedCoeff_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz
  have hfactor :
      0 <
        1 + |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| := by
    positivity
  nlinarith [hcoeff, hfactor, ha]

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_totalCoeffSum_nonpos_of_saturatedCoeff_pos_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonpos : SeedLiveShiftKernel.totalCoeffSum K ≤ 0)
    (ha : 0 < a)
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
  intro hB
  rcases hB with ⟨B, hCand⟩
  have hpos :=
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_pos_of_saturatedCoeff_pos_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz
  exact (not_le_of_gt hpos) hsum_nonpos

theorem WeightedObservable.not_exists_windowedColeHopfHeatShiftKernelTopDownBridge_eq_saturatedCandidate_of_totalCoeffSum_nonneg_of_saturatedCoeff_neg_of_stationary_shiftInvariant
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a c ν : ℝ)
    (hsum_nonneg : 0 ≤ SeedLiveShiftKernel.totalCoeffSum K)
    (ha : a < 0)
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
  intro hB
  rcases hB with ⟨B, hCand⟩
  have hneg :=
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_neg_of_saturatedCoeff_neg_of_topDownBridge_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν ha hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat B hCand hnz
  exact (not_le_of_gt hneg) hsum_nonneg
end WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
