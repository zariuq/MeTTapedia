/-
LLM Context:
- Histogram estimator: piecewise-constant function over bins
- Lipschitz regularity → within-bin variation bounded by diameter
- Error decomposition = bin-average error + PLN estimation error
-/
import Mettapedia.Logic.StratifiedPLN.LocalExchangeability

/-!
# Histogram Estimator for Stratified PLN

This file defines the histogram estimator: a piecewise-constant function
that assigns the PLN strength of each bin to all points in that bin.

## Main Definitions

* `histogramEstimator` - The piecewise-constant PLN estimator
* `LipschitzRegularity` - Lipschitz regularity assumption

## Main Theorems

* `withinBin_variation_bound` - Within-bin error bounded by Lipschitz × diameter
* `error_decomposition` - Total error ≤ PLN error + within-bin variation

## References

* Györfi et al., "A Distribution-Free Theory of Nonparametric Regression"
* Stone (1977), "Consistent Nonparametric Regression"
-/

namespace Mettapedia.Logic.StratifiedPLN

open Set MeasureTheory
open Mettapedia.Logic.EvidenceBeta

/-! ## PLN Strength Properties -/

section PLNStrengthProps

/-- PLN strength is non-negative. -/
theorem plnStrength_nonneg (n_pos n_neg : ℕ) : 0 ≤ plnStrength n_pos n_neg := by
  unfold plnStrength
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg n_pos
    · have : (0 : ℝ) ≤ n_pos := Nat.cast_nonneg n_pos
      have : (0 : ℝ) ≤ n_neg := Nat.cast_nonneg n_neg
      linarith

/-- PLN strength is at most 1. -/
theorem plnStrength_le_one (n_pos n_neg : ℕ) : plnStrength n_pos n_neg ≤ 1 := by
  unfold plnStrength
  split_ifs with h
  · exact zero_le_one
  · have hne : (n_pos + n_neg : ℝ) ≠ 0 := by
      simp only [ne_eq]
      exact_mod_cast h
    have hpos : 0 < (n_pos + n_neg : ℝ) := by
      have : 0 < n_pos + n_neg := Nat.pos_of_ne_zero h
      exact_mod_cast this
    rw [div_le_one hpos]
    have hp : (0 : ℝ) ≤ n_pos := Nat.cast_nonneg n_pos
    have hn : (0 : ℝ) ≤ n_neg := Nat.cast_nonneg n_neg
    linarith

end PLNStrengthProps

/-! ## The Histogram Estimator -/

section HistogramEstimator

variable {X : Type*} [MeasurableSpace X] {K : ℕ}

/-- The histogram PLN estimator: assigns PLN strength to each point based on bin.

    Given a partition and evidence counts per bin, this function returns
    the PLN strength k/(k+m) for the bin containing each point x. -/
noncomputable def histogramEstimator (partition : HistogramBins X K) (hK : 0 < K)
    (evidence : BinEvidence K) (x : X) : ℝ :=
  binPLNStrength evidence (partition.binIndex hK x)

/-- The histogram estimator is piecewise constant: same value for all x in same bin. -/
theorem histogramEstimator_constant_on_bin (partition : HistogramBins X K) (hK : 0 < K)
    (evidence : BinEvidence K) (i : Fin K) (x y : X)
    (hx : x ∈ partition.bins i) (hy : y ∈ partition.bins i) :
    histogramEstimator partition hK evidence x = histogramEstimator partition hK evidence y := by
  unfold histogramEstimator
  have hxi : partition.binIndex hK x = i := (partition.binIndex_eq_iff hK x i).mpr hx
  have hyi : partition.binIndex hK y = i := (partition.binIndex_eq_iff hK y i).mpr hy
  rw [hxi, hyi]

/-- The histogram estimator takes values in [0, 1]. -/
theorem histogramEstimator_mem_unit (partition : HistogramBins X K) (hK : 0 < K)
    (evidence : BinEvidence K) (x : X) :
    0 ≤ histogramEstimator partition hK evidence x ∧
    histogramEstimator partition hK evidence x ≤ 1 := by
  unfold histogramEstimator binPLNStrength
  exact ⟨plnStrength_nonneg _ _, plnStrength_le_one _ _⟩

end HistogramEstimator

/-! ## Lipschitz Regularity -/

section Regularity

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]

/-- Lipschitz bound on variation of a function.

    This captures the regularity assumption: the true regression function
    P(Y=1|X) varies smoothly with X, i.e., |f(x) - f(y)| ≤ L × dist(x, y).

    For logistic regression f(x) = σ(β·x), the sigmoid is 1/4-Lipschitz,
    so this holds with L = |β|/4. -/
structure LipschitzRegularity (f : X → ℝ) (L : ℝ) : Prop where
  lipschitz_nonneg : 0 ≤ L
  lipschitz_bound : ∀ x y : X, |f x - f y| ≤ L * dist x y

/-- Within any bin, function variation is bounded by Lipschitz × diameter.

    This is the key estimate: if f is L-Lipschitz and points x, y are in
    the same bin, then |f(x) - f(y)| ≤ L × diam(bin).

    Note: We need the bin to be bounded for this to hold. -/
theorem withinBin_variation_bound {f : X → ℝ} {L : ℝ} (hL : LipschitzRegularity f L)
    {K : ℕ} (partition : HistogramBins X K) (i : Fin K) (x y : X)
    (hx : x ∈ partition.bins i) (hy : y ∈ partition.bins i)
    (hbdd : Bornology.IsBounded (partition.bins i)) :
    |f x - f y| ≤ L * Metric.diam (partition.bins i) := by
  have hdist : dist x y ≤ Metric.diam (partition.bins i) :=
    Metric.dist_le_diam_of_mem hbdd hx hy
  calc |f x - f y|
    _ ≤ L * dist x y := hL.lipschitz_bound x y
    _ ≤ L * Metric.diam (partition.bins i) := by
        apply mul_le_mul_of_nonneg_left hdist hL.lipschitz_nonneg

end Regularity

/-! ## Error Decomposition -/

section ErrorDecomposition

variable {X : Type*} [MeasurableSpace X] {K : ℕ}

/-- Bayesian posterior mean for bin i based on evidence.

    This is what PLN strength converges to as sample size → ∞. -/
noncomputable def binBayesianMean (evidence : BinEvidence K) (i : Fin K) : ℝ :=
  uniformPosteriorMean (evidence.pos i) (evidence.neg i)

/-- Error decomposition for a single point.

    The total error |estimated - true| can be bounded by:
    1. PLN estimation error: |PLN strength - Bayesian mean|
    2. Within-bin variation: how much trueFunc varies within the bin

    This decomposition is the heart of the consistency proof. -/
theorem error_decomposition (partition : HistogramBins X K) (hK : 0 < K)
    (evidence : BinEvidence K) (x : X) (trueMean_x : ℝ) :
    let i := partition.binIndex hK x
    |histogramEstimator partition hK evidence x - trueMean_x| ≤
      |binPLNStrength evidence i - binBayesianMean evidence i| +
      |binBayesianMean evidence i - trueMean_x| := by
  intro i
  unfold histogramEstimator
  calc |binPLNStrength evidence i - trueMean_x|
    _ = |binPLNStrength evidence i - binBayesianMean evidence i +
         (binBayesianMean evidence i - trueMean_x)| := by ring_nf
    _ ≤ |binPLNStrength evidence i - binBayesianMean evidence i| +
         |binBayesianMean evidence i - trueMean_x| := abs_add_le _ _

/-- PLN error bound: The first term is O(1/n) from our main theorem. -/
theorem pln_error_term (evidence : BinEvidence K) (i : Fin K)
    (hne : evidence.pos i + evidence.neg i ≠ 0) :
    |binPLNStrength evidence i - binBayesianMean evidence i| ≤
      2 / ((evidence.pos i : ℝ) + (evidence.neg i : ℝ) + 2) := by
  unfold binBayesianMean
  exact binwise_error_bound evidence i hne

/-- Combined error bound for histogram estimator.

    Given:
    - PLN evidence per bin
    - True function variation within bin ≤ δ

    Total error ≤ 2/(n+2) + δ

    This shows: with enough samples and small enough bins, error → 0. -/
theorem combined_error_bound (partition : HistogramBins X K) (hK : 0 < K)
    (evidence : BinEvidence K) (x : X) (trueMean_x : ℝ)
    (hne : evidence.pos (partition.binIndex hK x) + evidence.neg (partition.binIndex hK x) ≠ 0)
    (δ : ℝ) (hδ : |binBayesianMean evidence (partition.binIndex hK x) - trueMean_x| ≤ δ) :
    |histogramEstimator partition hK evidence x - trueMean_x| ≤
      2 / ((evidence.pos (partition.binIndex hK x) : ℝ) +
           (evidence.neg (partition.binIndex hK x) : ℝ) + 2) + δ := by
  have h := error_decomposition partition hK evidence x trueMean_x
  simp only at h
  have h_pln := pln_error_term evidence (partition.binIndex hK x) hne
  linarith [h]

end ErrorDecomposition

/-! ## Convenience Lemmas for Consistency Proof -/

section ConsistencySetup

variable {X : Type*} [MeasurableSpace X] {K : ℕ}

/-- If all bins have at least N samples, PLN error in all bins is bounded. -/
theorem uniform_pln_error_bound (evidence : BinEvidence K) (N : ℕ) (hN : 0 < N)
    (hmin : ∀ i : Fin K, evidence.pos i + evidence.neg i ≥ N)
    (hK : 0 < K) (i : Fin K) :
    |binPLNStrength evidence i - binBayesianMean evidence i| ≤
      (2 : ℝ) / ((N : ℝ) + 2) := by
  -- Keep `hK` in the API (many callers already have it), and also satisfy the linter.
  have _ : 0 < K := hK
  have hne : evidence.pos i + evidence.neg i ≠ 0 := by
    have h := hmin i
    omega
  have h_bound := pln_error_term evidence i hne
  have h_N_le : (N : ℝ) ≤ (evidence.pos i : ℝ) + (evidence.neg i : ℝ) := by
    have := hmin i
    exact_mod_cast this
  have h_denom : (N : ℝ) + 2 ≤ (evidence.pos i : ℝ) + (evidence.neg i : ℝ) + 2 := by
    linarith
  have hN2_pos : (0 : ℝ) < (N : ℝ) + 2 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  calc |binPLNStrength evidence i - binBayesianMean evidence i|
    _ ≤ 2 / ((evidence.pos i : ℝ) + (evidence.neg i : ℝ) + 2) := h_bound
    _ ≤ (2 : ℝ) / ((N : ℝ) + 2) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hN2_pos h_denom

end ConsistencySetup

end Mettapedia.Logic.StratifiedPLN
