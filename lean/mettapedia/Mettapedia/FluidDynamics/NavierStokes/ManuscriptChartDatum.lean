import Mettapedia.FluidDynamics.NavierStokes.GeometricModeApproximation
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Manuscript-Flavored Chart Datum for the NS Grassroots Lane

This file upgrades the geometric finite-mode model into a closer analogue of
Appendix D.4 from the manuscript:

- a squared weighted chart radius;
- a bounded linear observable `ℓ`;
- the chart-cutoff datum `W₀ = χ · ℓ`;
- the Cole-Hopf datum `φ = exp(-W₀ / (2ν))`.

Everything remains finite-mode and local.  The point is to turn the D.4
formula shape into a concrete Lean model that feeds the already-existing
approximation and topology shells.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped BigOperators

section ManuscriptChartDatum

/-- Weighted squared contribution of the `n`-th mode to the chart radius. -/
def radiusSqTerm (x : ModeState) (n : ℕ) : ℝ :=
  (x.coeff n) ^ 2 * modeWeight n

/-- Squared weighted chart radius, closer to the manuscript's `‖κ(g)‖²`. -/
def radiusSq (x : ModeState) : ℝ :=
  ∑' n, radiusSqTerm x n

theorem summable_radiusSqTerm (x : ModeState) : Summable (radiusSqTerm x) := by
  refine Summable.of_norm_bounded summable_modeWeight ?_
  intro n
  have hsq : (x.coeff n) ^ 2 ≤ 1 := by
    simpa using (sq_le_one_iff_abs_le_one (x.coeff n)).2 (x.abs_le_one n)
  have hweight : 0 ≤ modeWeight n := by
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    unfold modeWeight
    exact inv_nonneg.mpr hpow
  calc
    ‖radiusSqTerm x n‖ = radiusSqTerm x n := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (sq_nonneg _) hweight
    _ = (x.coeff n) ^ 2 * modeWeight n := rfl
    _ ≤ modeWeight n := by
      simpa using mul_le_mul_of_nonneg_right hsq hweight

theorem radiusSqTerm_truncate_eq (x : ModeState) {N n : ℕ} (hn : n < N) :
    radiusSqTerm (truncateModes N x) n = radiusSqTerm x n := by
  simp [radiusSqTerm, truncateModes, hn]

theorem radiusSqTerm_truncate_eq_zero (x : ModeState) {N n : ℕ} (hn : N ≤ n) :
    radiusSqTerm (truncateModes N x) n = 0 := by
  simp [radiusSqTerm, truncateModes, not_lt.mpr hn]

theorem radiusSq_truncate_eq_sum (x : ModeState) (N : ℕ) :
    radiusSq (truncateModes N x) = Finset.sum (Finset.range N) (fun n => radiusSqTerm x n) := by
  rw [radiusSq, tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    exact radiusSqTerm_truncate_eq x (Finset.mem_range.mp hn)
  · intro n hn
    exact radiusSqTerm_truncate_eq_zero x (not_lt.mp (by simpa using hn))

theorem truncateModes_radiusSq_tendsto (x : ModeState) :
    Tendsto (fun N => radiusSq (truncateModes N x))
      Filter.atTop (nhds (radiusSq x)) := by
  convert (summable_radiusSqTerm x).hasSum.tendsto_sum_nat using 1
  ext N
  exact radiusSq_truncate_eq_sum x N

/-- A bounded coefficient family defining a manuscript-flavored linear
observable on the chart coordinates. -/
structure WeightedObservable where
  coeff : ℕ → ℝ
  boundConst : ℝ
  boundConst_nonneg : 0 ≤ boundConst
  coeff_bound : ∀ n, |coeff n| ≤ boundConst * modeWeight n

/-- The `n`-th contribution to the observable `ℓ(κ(g))`. -/
def observableTerm (L : WeightedObservable) (x : ModeState) (n : ℕ) : ℝ :=
  L.coeff n * x.coeff n

/-- The full bounded linear observable. -/
def matchingObservable (L : WeightedObservable) (x : ModeState) : ℝ :=
  ∑' n, observableTerm L x n

/-- The comparison envelope for the observable terms. -/
def observableEnvelope (L : WeightedObservable) (n : ℕ) : ℝ :=
  L.boundConst * modeWeight n

/-- Total envelope mass of the bounded observable. -/
def observableEnvelopeSum (L : WeightedObservable) : ℝ :=
  ∑' n, observableEnvelope L n

theorem summable_observableEnvelope (L : WeightedObservable) :
    Summable (observableEnvelope L) := by
  simpa [observableEnvelope] using summable_modeWeight.mul_left L.boundConst

theorem observableTerm_norm_le (L : WeightedObservable) (x : ModeState) (n : ℕ) :
    ‖observableTerm L x n‖ ≤ observableEnvelope L n := by
  have henv_nonneg : 0 ≤ observableEnvelope L n := by
    have hweight : 0 ≤ modeWeight n := by
      have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
      unfold modeWeight
      exact inv_nonneg.mpr hpow
    exact mul_nonneg L.boundConst_nonneg hweight
  calc
    ‖observableTerm L x n‖ = |L.coeff n| * |x.coeff n| := by
      simp [observableTerm]
    _ ≤ (L.boundConst * modeWeight n) * 1 := by
      have hmul :=
        mul_le_mul (L.coeff_bound n) (x.abs_le_one n) (abs_nonneg _)
          (by simpa [observableEnvelope] using henv_nonneg)
      simpa [observableEnvelope] using hmul
    _ = observableEnvelope L n := by
      simp [observableEnvelope]

theorem summable_observableTerm (L : WeightedObservable) (x : ModeState) :
    Summable (observableTerm L x) := by
  exact Summable.of_norm_bounded (summable_observableEnvelope L)
    (observableTerm_norm_le L x)

theorem observableTerm_truncate_eq (L : WeightedObservable) (x : ModeState) {N n : ℕ}
    (hn : n < N) :
    observableTerm L (truncateModes N x) n = observableTerm L x n := by
  simp [observableTerm, truncateModes, hn]

theorem observableTerm_truncate_eq_zero (L : WeightedObservable) (x : ModeState) {N n : ℕ}
    (hn : N ≤ n) :
    observableTerm L (truncateModes N x) n = 0 := by
  simp [observableTerm, truncateModes, not_lt.mpr hn]

theorem matchingObservable_truncate_eq_sum (L : WeightedObservable) (x : ModeState) (N : ℕ) :
    matchingObservable L (truncateModes N x) =
      Finset.sum (Finset.range N) (fun n => observableTerm L x n) := by
  rw [matchingObservable, tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl ?_
    intro n hn
    exact observableTerm_truncate_eq L x (Finset.mem_range.mp hn)
  · intro n hn
    exact observableTerm_truncate_eq_zero L x (not_lt.mp (by simpa using hn))

theorem truncateModes_matchingObservable_tendsto (L : WeightedObservable) (x : ModeState) :
    Tendsto (fun N => matchingObservable L (truncateModes N x))
      Filter.atTop (nhds (matchingObservable L x)) := by
  convert (summable_observableTerm L x).hasSum.tendsto_sum_nat using 1
  ext N
  exact matchingObservable_truncate_eq_sum L x N

/-- Concrete D.4-style approximation package on the geometric mode state. -/
def manuscriptApproximationData (L : WeightedObservable) :
    CutoffApproximationData radiusSq (matchingObservable L) where
  approx := truncateModes
  radius_tendsto := truncateModes_radiusSq_tendsto
  statistic_tendsto := truncateModes_matchingObservable_tendsto L

/-- Concrete chart-cutoff datum `W₀ = χ · ℓ`. -/
def manuscriptW0 (cutoff : ℝ → ℝ) (L : WeightedObservable) : ModeState → ℝ :=
  cutoffPotential cutoff radiusSq (matchingObservable L)

/-- Concrete chart heat datum `φ = exp(-W₀ / (2ν))`. -/
def manuscriptPhi (ν : ℝ) (cutoff : ℝ → ℝ) (L : WeightedObservable) : ModeState → ℝ :=
  coleHopfPhi ν (manuscriptW0 cutoff L)

theorem manuscriptW0_tendsto
    (L : WeightedObservable) {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N => manuscriptW0 cutoff L (truncateModes N x))
      Filter.atTop (nhds (manuscriptW0 cutoff L x)) := by
  exact (manuscriptApproximationData L).cutoffPotential_tendsto hcutoff x

theorem manuscriptPhi_tendsto
    (L : WeightedObservable) {ν : ℝ} {cutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (x : ModeState) :
    Tendsto (fun N => manuscriptPhi ν cutoff L (truncateModes N x))
      Filter.atTop (nhds (manuscriptPhi ν cutoff L x)) := by
  exact (manuscriptApproximationData L).coleHopfPhi_tendsto hcutoff x

theorem matchingObservable_abs_le
    (L : WeightedObservable) (x : ModeState) :
    |matchingObservable L x| ≤ observableEnvelopeSum L := by
  have hsumObs : HasSum (observableTerm L x) (matchingObservable L x) :=
    (summable_observableTerm L x).hasSum
  have hsumEnv : HasSum (observableEnvelope L) (observableEnvelopeSum L) :=
    (summable_observableEnvelope L).hasSum
  exact hsumObs.norm_le_of_bounded hsumEnv (observableTerm_norm_le L x)

theorem manuscriptW0_eq_zero_of_cutoff_eq_zero
    (L : WeightedObservable) {cutoff : ℝ → ℝ} {x : ModeState}
    (hcutoff : cutoff (radiusSq x) = 0) :
    manuscriptW0 cutoff L x = 0 := by
  simp [manuscriptW0, cutoffPotential, hcutoff]

theorem abs_manuscriptW0_le
    (L : WeightedObservable) {cutoff : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    |manuscriptW0 cutoff L x| ≤ B * observableEnvelopeSum L := by
  calc
    |manuscriptW0 cutoff L x|
      = |cutoff (radiusSq x)| * |matchingObservable L x| := by
          simp [manuscriptW0, cutoffPotential, abs_mul]
    _ ≤ B * observableEnvelopeSum L := by
      refine mul_le_mul (hcutoff _) (matchingObservable_abs_le L x) ?_ hB
      exact abs_nonneg _

theorem manuscriptPhi_pos
    (L : WeightedObservable) (ν : ℝ) {cutoff : ℝ → ℝ} (x : ModeState) :
    0 < manuscriptPhi ν cutoff L x := by
  simp [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar, Real.exp_pos]

theorem manuscriptPhi_lower_bound
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L x := by
  have hW := abs_manuscriptW0_le L hB hcutoff x
  have hW' := abs_le.mp hW
  have harg :
      -(B * observableEnvelopeSum L) / (2 * ν) ≤ -(manuscriptW0 cutoff L x) / (2 * ν) := by
    have hnum : -(B * observableEnvelopeSum L) ≤ -(manuscriptW0 cutoff L x) := by
      exact neg_le_neg hW'.2
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2 * ν)
  simpa [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar] using
    Real.exp_le_exp.mpr harg

theorem manuscriptPhi_upper_bound
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    manuscriptPhi ν cutoff L x ≤ Real.exp ((B * observableEnvelopeSum L) / (2 * ν)) := by
  have hW := abs_manuscriptW0_le L hB hcutoff x
  have hW' := abs_le.mp hW
  have harg :
      -(manuscriptW0 cutoff L x) / (2 * ν) ≤ (B * observableEnvelopeSum L) / (2 * ν) := by
    have hnum : -(manuscriptW0 cutoff L x) ≤ B * observableEnvelopeSum L := by
      have := neg_le_neg hW'.1
      simpa using this
    exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2 * ν)
  simpa [manuscriptPhi, manuscriptW0, coleHopfPhi, coleHopfScalar] using
    Real.exp_le_exp.mpr harg

theorem manuscriptPhi_bounded
    (L : WeightedObservable) {ν B : ℝ} (hν : 0 < ν) {cutoff : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hcutoff : ∀ r, |cutoff r| ≤ B)
    (x : ModeState) :
    Real.exp (-(B * observableEnvelopeSum L) / (2 * ν)) ≤ manuscriptPhi ν cutoff L x ∧
      manuscriptPhi ν cutoff L x ≤ Real.exp ((B * observableEnvelopeSum L) / (2 * ν)) := by
  exact ⟨manuscriptPhi_lower_bound L hν hB hcutoff x,
    manuscriptPhi_upper_bound L hν hB hcutoff x⟩

end ManuscriptChartDatum

end NavierStokes
end FluidDynamics
end Mettapedia
