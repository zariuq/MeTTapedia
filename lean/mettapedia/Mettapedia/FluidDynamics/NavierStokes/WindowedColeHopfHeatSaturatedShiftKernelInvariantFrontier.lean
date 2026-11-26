import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatShiftKernelFrontierCore
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedFrontier

/-!
# Invariant Frontier for Saturated Shift Kernels

This file records an honest constructive corridor for the nonlinear saturated
route inside the full finite shift-kernel shell.

If the concrete windowed vorticity tendril is:

- stationary between the seeded slice `t = 1` and the live slice,
- invariant under every seed and live shift used by the kernel,
- and has constant absolute magnitude `r`,

then any finite shift kernel whose total coefficient sum is `a / (1 + r)`
realizes the saturated candidate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

/-- The field agrees with its translation along every member of a shift family. -/
abbrev SeedLiveShiftKernel.IsShiftInvariantAlong {Index Time Space : Type*} [Add Space]
    (shift : Index → Space) (field : Time → Space → ℝ) : Prop :=
  ∀ i t y, field t (y + shift i) = field t y

/-- Every time slice has the vorticity of the reference slice. -/
abbrev UniformVorticityTendril.IsVorticityStationaryAt {Time Space : Type*}
    (reference : Time) (field : Time → Space → ℝ) : Prop :=
  ∀ t y, field reference y = field t y

namespace SeedLiveShiftKernel

/-- Total seeded mass of a finite shift kernel. -/
def seedCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  ∑ i, K.seedCoeff i

/-- Total live mass of a finite shift kernel. -/
def liveCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  ∑ i, K.liveCoeff i

/-- Total coefficient mass of a finite shift kernel. -/
def totalCoeffSum (K : SeedLiveShiftKernel κ X) : ℝ :=
  K.seedCoeffSum + K.liveCoeffSum

/-- A finite seed/live shift sum on an invariant field is multiplication
by the total coefficient mass. -/
theorem sum_shifted_eq_totalCoeffSum_mul {Time : Type*}
    (K : SeedLiveShiftKernel κ X) (field : Time → X → ℝ)
    (seedInvariant : IsShiftInvariantAlong K.seedShift field)
    (liveInvariant : IsShiftInvariantAlong K.liveShift field) (t : Time) (y : X) :
    (∑ i, (K.seedCoeff i * field t (y + K.seedShift i) +
      K.liveCoeff i * field t (y + K.liveShift i))) = K.totalCoeffSum * field t y := by
  calc
    _ = ∑ i, (K.seedCoeff i + K.liveCoeff i) * field t y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [seedInvariant i t y, liveInvariant i t y, add_mul]
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [totalCoeffSum, seedCoeffSum, liveCoeffSum, Finset.sum_add_distrib]

end SeedLiveShiftKernel

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).saturatedInitialSlice a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  funext y
  calc
    L.windowedColeHopfHeatShiftKernelInitialSlice
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x y
      = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)) := by
            simp [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice,
              UniformVorticityTendril.seedLiveOperatorInitialSlice,
              SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator, T]
    _ = SeedLiveShiftKernel.totalCoeffSum K * T.vorticity 1 y :=
      K.sum_shifted_eq_totalCoeffSum_mul T.vorticity hseedInv hliveInv 1 y
    _ = a * (T.vorticity 1 y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity 1 y / (1 + |T.vorticity 1 y|)) := by
          rw [habs 1 y]
    _ = T.saturatedInitialSlice a y := rfl

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).saturatedInitialSlice a := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
  funext y
  calc
    L.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x y
      = ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
          K.liveCoeff i * T.vorticity 1 (y + K.liveShift i)) := by
            simp [WeightedObservable.windowedColeHopfHeatShiftKernelInitialSlice_of_componentwise_abs_le,
              UniformVorticityTendril.seedLiveOperatorInitialSlice,
              SeedLiveShiftKernel.toSampleKernel, SeedLiveSampleKernel.toSeedLiveOperator, T]
    _ = SeedLiveShiftKernel.totalCoeffSum K * T.vorticity 1 y :=
      K.sum_shifted_eq_totalCoeffSum_mul T.vorticity hseedInv hliveInv 1 y
    _ = a * (T.vorticity 1 y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity 1 y / (1 + |T.vorticity 1 y|)) := by
          rw [habs 1 y]
    _ = T.saturatedInitialSlice a y := rfl

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
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
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
  unfold WeightedObservable.windowedColeHopfHeatShiftKernelCandidate
    WeightedObservable.windowedColeHopfHeatSaturatedCandidate
    UniformVorticityTendril.seedLiveOperatorCandidate UniformVorticityTendril.saturatedCandidate
  congr
  funext t y
  calc
    ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
        K.liveCoeff i * T.vorticity t (y + K.liveShift i))
      = ∑ i, (K.seedCoeff i + K.liveCoeff i) * T.vorticity t y := by
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
    _ = a * (T.vorticity t y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity t y / (1 + |T.vorticity t y|)) := by
          rw [habs t y]

theorem WeightedObservable.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hstat : UniformVorticityTendril.IsVorticityStationaryAt 1
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (habs :
      ∀ t : NNReal, ∀ y : X,
        |(L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity t y| = r) :
    L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  let T :=
    L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
  unfold WeightedObservable.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
    WeightedObservable.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
    UniformVorticityTendril.seedLiveOperatorCandidate UniformVorticityTendril.saturatedCandidate
  congr
  funext t y
  calc
    ∑ i, (K.seedCoeff i * T.vorticity 1 (y + K.seedShift i) +
        K.liveCoeff i * T.vorticity t (y + K.liveShift i))
      = ∑ i, (K.seedCoeff i + K.liveCoeff i) * T.vorticity t y := by
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
    _ = a * (T.vorticity t y / (1 + r)) := by
          rw [hcoeff]
          ring
    _ = a * (T.vorticity t y / (1 + |T.vorticity t y|)) := by
          rw [habs t y]

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x).vorticity)
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
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice,
      L.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude
        (ι := ι) (X := X)
        (selector := selector) (K := K) (a := a) (r := r) (c := c) (ν := ν)
        (hc := hc) (hν := hν) (curlFrame := curlFrame) (curlBound := curlBound)
        (curlBound_nonneg := curlBound_nonneg) (hcurl := hcurl) (x := x)
        hcoeff hseedInv hliveInv habs]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause
        (ι := ι) (X := X)
        selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
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
          selector a c ν hc hν
          curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) := by
  simpa [WeightedObservable.windowedColeHopfHeatSaturatedInitialSlice_of_componentwise_abs_le,
      L.windowedColeHopfHeatSaturatedShiftKernelInitialSlice_eq_saturatedInitialSlice_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
        (ι := ι) (X := X)
        (selector := selector) (K := K) (a := a) (r := r) (c := c) (ν := ν)
        (hc := hc) (hν := hν) (curlFrame := curlFrame)
        (curlComponentBound := curlComponentBound)
        (hcurlComponentBound_nonneg := hcurlComponentBound_nonneg)
        (hcurl := hcurl) (x := x)
        hcoeff hseedInv hliveInv habs]
    using
      (L.windowedColeHopfHeat_realizes_shiftKernel_pressure_seeded_clause_of_componentwise_abs_le
        (ι := ι) (X := X)
        selector K c ν hc hν
        curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
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
              selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector K a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hseedInv hliveInv hstat habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (K : SeedLiveShiftKernel κ X)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff : SeedLiveShiftKernel.totalCoeffSum K = a / (1 + r))
    (hseedInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.seedShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
    (hliveInv : SeedLiveShiftKernel.IsShiftInvariantAlong K.liveShift
      (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
          (ι := ι) (X := X)
          selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x).vorticity)
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
              selector K c ν hc hν
              curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred
            (Time := NNReal) (X := X) K)
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν
            curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector K c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector K a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeff hseedInv hliveInv hstat habs

end WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
