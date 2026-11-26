import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatSaturatedShiftKernelInvariantFrontier
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatMaskedShiftKernelObstruction

/-!
# Saturated Frontier for the Masked Common-Shift Kernel Family

This file specializes the constructive saturated finite shift-kernel corridor
to the older masked common-shift family.

Every seed term uses the same spatial shift `s`, while each live term either
stays at `x` or moves to `x + s` according to the Boolean mask.  So the full
per-anchor invariance assumptions of the generic shift-kernel theorem collapse
to a single shift-invariance hypothesis for that common shift.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontier

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X]

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
    L.windowedColeHopfHeatShiftKernelCandidate
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff
      (by
        intro i t y
        simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hshiftInv t y)
      (by
        intro i t y
        by_cases hmask : mask i = true
        · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshiftInv t y
        · simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask, add_zero])
      hstat habs

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_maskedShiftKernel_of_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
          selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a r c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff
      (by
        intro i t y
        simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hshiftInv t y)
      (by
        intro i t y
        by_cases hmask : mask i = true
        · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshiftInv t y
        · simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask, add_zero])
      habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedMaskedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge
    (ι := ι) (X := X)
    selector
    (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
      (X := X) mask s seedCoeff liveCoeff)
    c ν hc hν curlFrame curlBound curlBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatMaskedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a r c ν hc hν
      curlFrame curlBound curlBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

theorem WeightedObservable.windowedColeHopfHeatMaskedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
    L.windowedColeHopfHeatShiftKernelCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x =
    L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  exact
    L.windowedColeHopfHeatSaturatedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a r c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeff
      (by
        intro i t y
        simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hshiftInv t y)
      (by
        intro i t y
        by_cases hmask : mask i = true
        · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshiftInv t y
        · simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask, add_zero])
      hstat habs

theorem WeightedObservable.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_maskedShiftKernel_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
          selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x)) := by
  exact
    L.windowedColeHopfHeat_realizes_saturated_pressure_seeded_clause_via_shiftKernel_of_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector
      (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
        (X := X) mask s seedCoeff liveCoeff)
      a r c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeff
      (by
        intro i t y
        simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel] using hshiftInv t y)
      (by
        intro i t y
        by_cases hmask : mask i = true
        · simpa [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask] using hshiftInv t y
        · simp [SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel, hmask, add_zero])
      habs

theorem WeightedObservable.exists_windowedColeHopfHeatSaturatedMaskedShiftKernelBridge_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (mask : κ → Bool)
    (s : X)
    (seedCoeff liveCoeff : κ → ℝ)
    (a r c ν : ℝ)
    (hc : 0 < c)
    (hν : 0 < ν)
    (curlFrame : ι → X → ℝ)
    (curlComponentBound : ℝ)
    (hcurlComponentBound_nonneg : 0 ≤ curlComponentBound)
    (hcurl : ∀ x i, |curlFrame i x| ≤ curlComponentBound)
    (x : ModeState)
    (hcoeff :
      SeedLiveShiftKernel.totalCoeffSum
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) = a / (1 + r))
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
              selector
              (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
                (X := X) mask s seedCoeff liveCoeff)
              c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x))
          (shiftKernelCompatibilityPred (Time := NNReal) (X := X)
            (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
              (X := X) mask s seedCoeff liveCoeff))
          (L.windowedColeHopfHeatUniformVorticityTendril_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x),
        B.candidate =
          L.windowedColeHopfHeatSaturatedCandidate_of_componentwise_abs_le
            (ι := ι) (X := X)
            selector a c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x := by
  refine ⟨L.toWindowedColeHopfHeatShiftKernelBridge_of_componentwise_abs_le
    (ι := ι) (X := X)
    selector
    (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
      (X := X) mask s seedCoeff liveCoeff)
    c ν hc hν curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x, ?_⟩
  exact
    L.windowedColeHopfHeatMaskedShiftKernelCandidate_eq_saturatedCandidate_of_stationary_shiftInvariant_constantMagnitude_of_componentwise_abs_le
      (ι := ι) (X := X)
      selector mask s seedCoeff liveCoeff a r c ν hc hν
      curlFrame curlComponentBound hcurlComponentBound_nonneg hcurl x
      hcoeff hshiftInv hstat habs

end WindowedColeHopfHeatSaturatedMaskedShiftKernelFrontier

end NavierStokes
end FluidDynamics
end Mettapedia
