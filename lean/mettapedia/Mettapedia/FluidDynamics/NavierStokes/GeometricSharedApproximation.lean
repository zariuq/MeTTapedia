import Mettapedia.FluidDynamics.NavierStokes.ManuscriptChartDatum
import Mettapedia.FluidDynamics.NavierStokes.SharedApproximationPackage
import Mettapedia.ProbabilityTheory.MarkovCategory.Kernels

/-!
# Explicit Shared Geometric Approximation Instance

This file provides the first fully explicit instance of the shared
approximation architecture:

- the common approximation family is `truncateModes`;
- the chart side is the concrete D.4-style datum from `ManuscriptChartDatum`;
- the identity side reads off finitely many selected coefficients from the same
  truncated state;
- positivity and energy bounds hold uniformly, not merely eventually.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open ProbabilityTheory
open Mettapedia.ProbabilityTheory
open scoped BigOperators

section GeometricSharedApproximation

variable {Time ι X : Type*}
variable [One Time] [Mul Time] [Fintype ι]

/-- Every fixed mode eventually survives the finite-mode truncation unchanged. -/
theorem truncateModes_coeff_tendsto (x : ModeState) (k : ℕ) :
    Tendsto (fun N => (truncateModes N x).coeff k) Filter.atTop (nhds (x.coeff k)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop k] with N hN
  simp [truncateModes, hN]

/-- Finite selections of bounded coefficients always have uniformly bounded
finite carré-du-champ energy. -/
theorem gamma_selectedCoeff_le_card (selector : ι → ℕ) (x : ModeState) :
    gamma (fun i => x.coeff (selector i)) ≤ (Fintype.card ι : ℝ) := by
  unfold gamma
  calc
    ∑ i, (x.coeff (selector i)) ^ 2 ≤ ∑ i, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hsquare : (x.coeff (selector i)) ^ 2 ≤ 1 := by
        simpa using (sq_le_one_iff_abs_le_one (x.coeff (selector i))).2
          (x.abs_le_one (selector i))
      simpa using hsquare
    _ = (Fintype.card ι : ℝ) := by simp

/-- Time-independent positive field built from the concrete chart observable. -/
def WeightedObservable.modePhi (L : WeightedObservable) (phiOffset : ℝ) :
    ModeState → Time → ℝ :=
  fun x _ => phiOffset + matchingObservable L x

/-- The uniform lower bound extracted from `phiOffset`. -/
def WeightedObservable.modeMPhi (L : WeightedObservable) (phiOffset : ℝ) : ℝ :=
  phiOffset - observableEnvelopeSum L

omit [One Time] [Mul Time] [Fintype ι] in
theorem WeightedObservable.modePhi_lower
    (L : WeightedObservable) (phiOffset : ℝ) (x : ModeState) (t : Time) :
    L.modeMPhi phiOffset ≤ L.modePhi phiOffset x t := by
  have habs := matchingObservable_abs_le L x
  have hlow : -observableEnvelopeSum L ≤ matchingObservable L x := (abs_le.mp habs).1
  dsimp [WeightedObservable.modeMPhi, WeightedObservable.modePhi]
  linarith

/-- The time-independent field built from selected coefficients. -/
def selectedDerivative (selector : ι → ℕ) : ModeState → Time → ι → ℝ :=
  fun x _ i => x.coeff (selector i)

omit [One Time] [Mul Time] [Fintype ι] in
theorem selectedDerivative_tendsto
    (selector : ι → ℕ) (x : ModeState) (t : Time) (i : ι) :
    Tendsto (fun N => selectedDerivative selector (truncateModes N x) t i)
      Filter.atTop (nhds (selectedDerivative selector x t i)) := by
  simpa [selectedDerivative] using truncateModes_coeff_tendsto x (selector i)

omit [One Time] [Mul Time] in
theorem selectedDerivative_energy_le
    (selector : ι → ℕ) (x : ModeState) (t : Time) :
    gamma (fun i => selectedDerivative selector x t i) ≤ (Fintype.card ι : ℝ) := by
  simpa [selectedDerivative] using gamma_selectedCoeff_le_card selector x

/-- Trivial local kernel semigroup used to keep the shared approximation object
fully inhabited while remaining analytically honest. -/
def trivialKernelSemigroupData : KernelSemigroupData (Time := Time) where
  Ω := kernelMarkovUnitObj
  evolve := fun _ => (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel kernelMarkovUnitObj kernelMarkovUnitObj)
  evolve_one := rfl
  evolve_mul := by
    intro s t
    exact ProbabilityTheory.Kernel.comp_id _

/-- First explicit shared approximation instance on the geometric mode state. -/
def WeightedObservable.geometricSharedApproximation
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (phiOffset : ℝ)
    (hphi : observableEnvelopeSum L < phiOffset)
    (ν : ℝ)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound) :
    SharedApproximationPackage (Time := Time) (ι := ι) (X := X)
      radiusSq (matchingObservable L) where
  toKernelSemigroupData := trivialKernelSemigroupData
  approx := truncateModes
  radius_tendsto := truncateModes_radiusSq_tendsto
  statistic_tendsto := truncateModes_matchingObservable_tendsto L
  Phi := L.modePhi phiOffset
  dPhi := selectedDerivative selector
  ν := ν
  mPhi := L.modeMPhi phiOffset
  energyBound := (Fintype.card ι : ℝ)
  curlFrame := curlFrame
  curlBound := curlBound
  mPhi_pos := by
    dsimp [WeightedObservable.modeMPhi]
    linarith
  energyBound_nonneg := by positivity
  curlBound_nonneg := curlBound_nonneg
  Phi_tendsto := by
    intro x t
    dsimp [WeightedObservable.modePhi]
    simpa using (truncateModes_matchingObservable_tendsto L x).const_add phiOffset
  dPhi_tendsto := by
    intro x t i
    exact selectedDerivative_tendsto selector x t i
  Phi_lower_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [WeightedObservable.modePhi, WeightedObservable.modeMPhi] using
        L.modePhi_lower phiOffset (truncateModes n x) t
  dPhi_energy_eventually := by
    intro x t
    exact Eventually.of_forall fun n => by
      simpa [selectedDerivative] using
        selectedDerivative_energy_le selector (truncateModes n x) t
  curl_energy := hcurl

theorem WeightedObservable.geometricSharedApproximation_Phi_lower_eventually
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (phiOffset : ℝ)
    (hphi : observableEnvelopeSum L < phiOffset)
    (ν : ℝ)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) (t : Time) :
    ∀ᶠ n in Filter.atTop,
      L.modeMPhi phiOffset ≤ L.modePhi phiOffset (truncateModes n x) t := by
  exact (L.geometricSharedApproximation
    (Time := Time) (ι := ι) (X := X)
    selector phiOffset hphi ν curlFrame curlBound curlBound_nonneg hcurl).Phi_lower_eventually x t

theorem WeightedObservable.geometricSharedApproximation_dPhi_energy_eventually
    (L : WeightedObservable)
    (selector : ι → ℕ)
    (phiOffset : ℝ)
    (hphi : observableEnvelopeSum L < phiOffset)
    (ν : ℝ)
    (curlFrame : ι → X → ℝ)
    (curlBound : ℝ)
    (curlBound_nonneg : 0 ≤ curlBound)
    (hcurl : ∀ x, gamma (fun i => curlFrame i x) ≤ curlBound)
    (x : ModeState) (t : Time) :
    ∀ᶠ n in Filter.atTop,
      gamma (fun i => selectedDerivative selector (truncateModes n x) t i) ≤ (Fintype.card ι : ℝ) := by
  exact (L.geometricSharedApproximation
    (Time := Time) (ι := ι) (X := X)
    selector phiOffset hphi ν curlFrame curlBound curlBound_nonneg hcurl).dPhi_energy_eventually x t

end GeometricSharedApproximation

end NavierStokes
end FluidDynamics
end Mettapedia
