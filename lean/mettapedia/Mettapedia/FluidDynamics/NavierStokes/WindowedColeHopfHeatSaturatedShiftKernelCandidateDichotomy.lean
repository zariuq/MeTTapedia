import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelCandidateBounds

/-!
# Windowed Cole-Hopf Saturated Shift-Kernel: CandidateDichotomy

Candidate-level equal-magnitude and witness-dichotomy consequences for invariant saturated candidates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
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
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
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
  have hEqPoint (t : NNReal) (y : X) :
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
                exact congrFun (congrFun (congrArg VelocityPressureCandidate.velocity hCand.symm) t) y
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
  have hCoeffFormula (t : NNReal) (y : X)
      (hnz : T.vorticity t y ≠ 0) :
      SeedLiveShiftKernel.totalCoeffSum K * (1 + |T.vorticity t y|) = a := by
    let w := T.vorticity t y
    have hw :
        a * (w / (1 + |w|)) = SeedLiveShiftKernel.totalCoeffSum K * w := by
      simpa [w] using hEqPoint t y
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
    · linarith
    · exact False.elim (hnz hwzero)
  have h1 :
      SeedLiveShiftKernel.totalCoeffSum K * (1 + |T.vorticity t₁ y₁|) = a :=
    hCoeffFormula t₁ y₁ hnz₁
  have h2 :
      SeedLiveShiftKernel.totalCoeffSum K * (1 + |T.vorticity t₂ y₂|) = a :=
    hCoeffFormula t₂ y₂ hnz₂
  have hzero :
      SeedLiveShiftKernel.totalCoeffSum K *
        (|T.vorticity t₁ y₁| - |T.vorticity t₂ y₂|) = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp hzero with hsum0 | habs
  · exact False.elim (hsum hsum0)
  · linarith

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_or_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
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
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
    {t₁ t₂ : NNReal} {y₁ y₂ : X}
    (hnz₁ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁ ≠ 0)
    (hnz₂ :
      (L.windowedColeHopfHeatUniformVorticityTendril
        (ι := ι) (X := X)
        selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂ ≠ 0) :
    SeedLiveShiftKernel.totalCoeffSum K = 0 ∨
      |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₁ y₁| =
        |(L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t₂ y₂| := by
  by_cases hsum : SeedLiveShiftKernel.totalCoeffSum K = 0
  · exact Or.inl hsum
  · exact Or.inr <|
      L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
        (ι := ι) (X := X)
        selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
        hseedInv hliveInv hstat hCand hnz₁ hnz₂

theorem WeightedObservable.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_of_candidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
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
    (hCand :
      L.windowedColeHopfHeatShiftKernelCandidate
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
      L.windowedColeHopfHeatSaturatedCandidate
        (ι := ι) (X := X)
        selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)
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
    SeedLiveShiftKernel.totalCoeffSum K = 0 := by
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habsNe⟩
  have hZeroOr :=
    L.windowedColeHopfHeatShiftKernel_totalCoeffSum_zero_or_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz₁ hnz₂
  rcases hZeroOr with hsum | habs
  · exact hsum
  · exact False.elim (habsNe habs)

theorem WeightedObservable.not_windowedColeHopfHeatShiftKernelCandidate_eq_saturatedCandidate_of_abs_ne_abs_of_stationary_shiftInvariant
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
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x ≠
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  intro hCand
  rcases hwitness with ⟨t₁, t₂, y₁, y₂, hnz₁, hnz₂, habs⟩
  have hEq :=
    L.windowedColeHopfHeatShiftKernel_abs_eq_abs_of_candidate_eq_saturatedCandidate_of_stationary_shiftInvariant
      (ι := ι) (X := X)
      selector K a c ν hsum hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hseedInv hliveInv hstat hCand hnz₁ hnz₂
  exact habs hEq
end WindowedColeHopfHeatSaturatedShiftKernelInvariantObstruction

end NavierStokes
end FluidDynamics
end Mettapedia
