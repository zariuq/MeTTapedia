/-
# Distributional Inference Convergence

Proves that PLN scalar inference *converges to distributional inference*
in the high-evidence limit: as evidence counts grow, both the exact
deduction variance and the heuristic-implied variance tend to zero,
and therefore the approximation error between them vanishes.

This complements PLNDistributionalChainDominance.lean:
- The dominance file shows scalar inference is *wrong* in the finite regime.
- This file shows scalar inference is *asymptotically correct*.
Together they establish that distributional inference (PLN book Ch. 6) is
strictly necessary in the finite-evidence regime where PLN actually operates.

## Key results

1. `scaledEvidence`: Evidence(k·p₀, k·n₀) with constant strength.
2. `beta_variance_scaled_eq`: exact variance formula in terms of k.
3. `beta_variance_vanishes`: Beta variance → 0 as k → ∞.
4. `exact_variance_vanishes_of_input_variance`: exact deduction variance → 0.
5. `implied_variance_vanishes`: heuristic-implied variance → 0.
6. `approximation_error_vanishes`: |exact - implied| → 0.
7. `scalar_converges_to_distributional`: summary theorem.

## References

- Goertzel et al., "Probabilistic Logic Networks" (Springer, 2008), Chapter 6
- PLNDistributionalChainDominance.lean (this project)
- PLNDistributional.lean (this project): Beta–STV bridge, variance audit
-/

import Mettapedia.Logic.PLNDistributionalChainDominance

noncomputable section

namespace Mettapedia.Logic.PLN.DistributionalConvergence

open Mettapedia.Logic.PLN.Distributional
open Mettapedia.Logic.PLN.DistributionalChainDominance
open Mettapedia.Logic.PLNDeduction
open Set

/-! ## Step 1: Scaled Evidence -/

/-- Scale evidence counts by a positive natural number k.
    Evidence(k·p₀, k·n₀) represents k times as much evidence
    with the same strength ratio. -/
def scaledEvidence (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) : Evidence where
  positive := k * p₀
  negative := k * n₀
  positive_pos := mul_pos (Nat.cast_pos.mpr hk) hp
  negative_pos := mul_pos (Nat.cast_pos.mpr hk) hn

/-- Scaled evidence has constant strength = p₀/(p₀+n₀), independent of k. -/
theorem scaledEvidence_strength (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) :
    (scaledEvidence p₀ n₀ hp hn k hk).strength = p₀ / (p₀ + n₀) := by
  simp only [scaledEvidence, Evidence.strength, Evidence.total]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Scaled evidence total = k·(p₀+n₀). -/
theorem scaledEvidence_total (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) :
    (scaledEvidence p₀ n₀ hp hn k hk).total = k * (p₀ + n₀) := by
  simp only [scaledEvidence, Evidence.total]; ring

/-! ## Step 2: Beta Variance Vanishes -/

/-- The Beta variance of scaled evidence in closed form. -/
theorem beta_variance_scaled_eq (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) :
    (scaledEvidence p₀ n₀ hp hn k hk).variance =
    (k * p₀) * (k * n₀) / ((k * (p₀ + n₀))^2 * (k * (p₀ + n₀) + 1)) := by
  simp only [Evidence.variance, Evidence.toBeta, BetaParams.variance, BetaParams.n, scaledEvidence]
  congr 1; ring

/-- Upper bound: Beta variance ≤ p₀·n₀ / (k·(p₀+n₀)³). -/
theorem beta_variance_scaled_le (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) :
    (scaledEvidence p₀ n₀ hp hn k hk).variance ≤
    p₀ * n₀ / (k * (p₀ + n₀)^3) := by
  rw [beta_variance_scaled_eq]
  have hT : 0 < p₀ + n₀ := by linarith
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkT : 0 < k * (p₀ + n₀) := mul_pos hk' hT
  have hden1 : 0 < (k * (p₀ + n₀))^2 * (k * (p₀ + n₀) + 1) :=
    mul_pos (sq_pos_of_pos hkT) (by linarith)
  have hden2 : 0 < k * (p₀ + n₀)^3 := mul_pos hk' (pow_pos hT 3)
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [sq_nonneg (k : ℝ), sq_nonneg (p₀ + n₀),
             mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hk') (le_of_lt hk'))
               (le_of_lt hp)) (le_of_lt hn),
             mul_nonneg (mul_nonneg (le_of_lt hp) (le_of_lt hn))
               (sq_nonneg (p₀ + n₀))]

/-- Beta variance vanishes as k → ∞. -/
theorem beta_variance_vanishes (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
    (scaledEvidence p₀ n₀ hp hn k hk).variance < ε := by
  intro ε hε
  set C := p₀ * n₀ / (p₀ + n₀)^3
  have hT : 0 < p₀ + n₀ := by linarith
  have hC_pos : 0 < C := div_pos (mul_pos hp hn) (pow_pos hT 3)
  use Nat.ceil (C / ε) + 1
  intro k hk hk_pos
  calc (scaledEvidence p₀ n₀ hp hn k hk_pos).variance
      ≤ p₀ * n₀ / (k * (p₀ + n₀)^3) := beta_variance_scaled_le p₀ n₀ hp hn k hk_pos
    _ = C / k := by simp only [C]; field_simp
    _ < ε := by
        have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
        rw [div_lt_iff₀ hk']
        have h1 : (↑(Nat.ceil (C / ε) + 1) : ℝ) ≤ k := Nat.cast_le.mpr hk
        have h2 : C / ε ≤ ↑(Nat.ceil (C / ε)) := Nat.le_ceil _
        push_cast at h1
        have h3 : C ≤ ε * ↑(Nat.ceil (C / ε)) := by
          have := (div_le_iff₀ hε).mp (le_trans (le_refl _) h2)
          linarith
        nlinarith [mul_nonneg (le_of_lt hε) (Nat.cast_nonneg (Nat.ceil (C / ε)))]

/-! ## Step 3: Exact Deduction Variance Vanishes -/

/-- The sum-of-squares form of varianceAffineProductIndep is bounded linearly
    in the input variances when both are small (≤ 1). -/
theorem varianceAffineProductIndep_le_linear
    (μX μY a b c δ σ2X σ2Y : ℝ)
    (_hσX_nn : 0 ≤ σ2X) (hσY_nn : 0 ≤ σ2Y)
    (hσX : σ2X ≤ δ) (hσY : σ2Y ≤ δ)
    (hδ_nn : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    varianceAffineProductIndep μX μY σ2X σ2Y a b c ≤
    ((a * μY + b)^2 + (a * μX + c)^2 + a^2) * δ := by
  have h_sos : varianceAffineProductIndep μX μY σ2X σ2Y a b c =
      (a*μY + b)^2 * σ2X + (a*μX + c)^2 * σ2Y + a^2 * σ2X * σ2Y := by
    simp only [varianceAffineProductIndep, varianceProductIndep]; ring
  rw [h_sos]
  have h1 : (a*μY + b)^2 * σ2X ≤ (a*μY + b)^2 * δ :=
    mul_le_mul_of_nonneg_left hσX (sq_nonneg _)
  have h2 : (a*μX + c)^2 * σ2Y ≤ (a*μX + c)^2 * δ :=
    mul_le_mul_of_nonneg_left hσY (sq_nonneg _)
  have h3 : a^2 * σ2X * σ2Y ≤ a^2 * δ := by
    calc a^2 * σ2X * σ2Y ≤ a^2 * δ * δ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hσX (sq_nonneg _)) hσY
            hσY_nn (mul_nonneg (sq_nonneg _) hδ_nn)
      _ ≤ a^2 * δ * 1 :=
          mul_le_mul_of_nonneg_left hδ1 (mul_nonneg (sq_nonneg _) hδ_nn)
      _ = a^2 * δ := by ring
  linarith

/-- A distributional chain step built from scaled evidence. -/
def scaledStep (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (sB sC : ℝ) (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1)
    (k : ℕ) (hk : 0 < k) : DistributionalChainStep where
  evidence_AB := scaledEvidence p₀ n₀ hp hn k hk
  evidence_BC := scaledEvidence p₀ n₀ hp hn k hk
  sB := sB
  sC := sC
  sB_pos := hsB
  sB_lt_one := hsB1
  sC_nonneg := hsC0
  sC_le_one := hsC1

/-- Exact deduction variance vanishes as input variances vanish. -/
theorem exact_variance_vanishes_of_input_variance
    (μX μY sB sC : ℝ) (hB : sB ≠ 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ σ2X σ2Y : ℝ,
    0 ≤ σ2X → 0 ≤ σ2Y → σ2X < δ → σ2Y < δ →
    trueFullDeductionVariance μX μY σ2X σ2Y sB sC hB < ε := by
  intro ε hε
  set ac := plnDeductionCoeffs sB sC hB
  set a := ac.1; set b := ac.2.1; set c := ac.2.2.1
  set K := (a * μY + b)^2 + (a * μX + c)^2 + a^2
  have hK_nn : 0 ≤ K := by positivity
  have hK1 : 0 < K + 1 := by linarith
  set δ := min 1 (ε / (K + 1))
  have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨by norm_num, div_pos hε hK1⟩
  refine ⟨δ, hδ_pos, fun σ2X σ2Y hσX_nn hσY_nn hσX hσY => ?_⟩
  unfold trueFullDeductionVariance
  show varianceAffineProductIndep μX μY σ2X σ2Y a b c < ε
  calc varianceAffineProductIndep μX μY σ2X σ2Y a b c
      ≤ K * δ := by
        have := varianceAffineProductIndep_le_linear μX μY a b c δ σ2X σ2Y
          hσX_nn hσY_nn (le_of_lt hσX) (le_of_lt hσY) (le_of_lt hδ_pos) (min_le_left _ _)
        linarith
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK_nn
    _ < ε := by
        rcases eq_or_lt_of_le hK_nn with hK0 | hK_pos
        · simp [← hK0]; exact hε
        · calc K * (ε / (K + 1)) = K / (K + 1) * ε := by ring
            _ < 1 * ε := by
                apply mul_lt_mul_of_pos_right _ hε
                rw [div_lt_one hK1]; linarith
            _ = ε := one_mul ε

/-! ## Step 4: Implied Variance Vanishes -/

/-- When c_h < 1, implied variance = s·(1-s)·(1-c_h). -/
theorem impliedVariance_eq (step : ScalarChainStep)
    (hc_lt : step.heuristicConfidence < 1) :
    step.impliedVariance =
    step.outputStrength * (1 - step.outputStrength) * (1 - step.heuristicConfidence) := by
  simp only [ScalarChainStep.impliedVariance]
  have h_pos : 0 < 1 - step.heuristicConfidence := by linarith
  have hne : (1 : ℝ) - step.heuristicConfidence ≠ 0 := ne_of_gt h_pos
  field_simp
  ring

/-- The confidence of scaledEvidence = k·T₀/(k·T₀+1). -/
theorem scaledEvidence_confidence (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (k : ℕ) (hk : 0 < k) :
    (scaledEvidence p₀ n₀ hp hn k hk).toBeta.toSTV.confidence =
    k * (p₀ + n₀) / (k * (p₀ + n₀) + 1) := by
  simp only [BetaParams.toSTV, BetaParams.n, Evidence.toBeta, scaledEvidence]
  congr 1 <;> ring

/-- The heuristic confidence of a scaledStep. -/
theorem scaledStep_heuristicConfidence (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (sB sC : ℝ) (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1)
    (k : ℕ) (hk : 0 < k) :
    (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).toScalar.heuristicConfidence =
    (k * (p₀ + n₀) / (k * (p₀ + n₀) + 1))^2 := by
  simp only [DistributionalChainStep.toScalar, ScalarChainStep.heuristicConfidence, scaledStep]
  rw [scaledEvidence_confidence]; ring

/-- The heuristic confidence of a scaledStep is < 1. -/
theorem scaledStep_hc_lt_one (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (sB sC : ℝ) (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1)
    (k : ℕ) (hk : 0 < k) :
    (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).toScalar.heuristicConfidence < 1 := by
  rw [scaledStep_heuristicConfidence]
  have hT : 0 < p₀ + n₀ := by linarith
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hden : 0 < k * (p₀ + n₀) + 1 := by positivity
  have hfrac_lt : k * (p₀ + n₀) / (k * (p₀ + n₀) + 1) < 1 := by
    rw [div_lt_one hden]; linarith
  have hfrac_nn : 0 ≤ k * (p₀ + n₀) / (k * (p₀ + n₀) + 1) :=
    div_nonneg (by positivity) (by positivity)
  calc (k * (p₀ + n₀) / (k * (p₀ + n₀) + 1))^2
      < 1^2 := sq_lt_sq' (by linarith) hfrac_lt
    _ = 1 := one_pow 2

/-- The output strength of a scaledStep is constant in k. -/
theorem scaledStep_outputStrength_const (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (sB sC : ℝ) (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1)
    (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k₁ hk₁).toScalar.outputStrength =
    (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k₂ hk₂).toScalar.outputStrength := by
  simp only [DistributionalChainStep.toScalar, ScalarChainStep.outputStrength, scaledStep]
  have h1 := scaledEvidence_strength p₀ n₀ hp hn k₁ hk₁
  have h2 := scaledEvidence_strength p₀ n₀ hp hn k₂ hk₂
  simp only [BetaParams.toSTV, BetaParams.expectedValue, BetaParams.n,
             Evidence.toBeta, Evidence.strength, Evidence.total, scaledEvidence] at *
  rw [h1, h2]

/-- The confidence gap 1 - c_h of a scaledStep converges to 0 as k → ∞.
    Concretely: 1 - c_h ≤ (2k·T₀+1)/(k·T₀+1)² ≤ 3/(k·T₀). -/
theorem scaledStep_confidence_gap_le (p₀ n₀ : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (sB sC : ℝ) (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1)
    (k : ℕ) (hk : 0 < k) :
    1 - (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).toScalar.heuristicConfidence ≤
    3 / (k * (p₀ + n₀)) := by
  rw [scaledStep_heuristicConfidence]
  set T := p₀ + n₀
  have hT : 0 < T := by linarith
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkT : 0 < k * T := mul_pos hk' hT
  have hden : 0 < k * T + 1 := by linarith
  -- 1 - (kT/(kT+1))² = ((kT+1)² - (kT)²)/(kT+1)² = (2kT+1)/(kT+1)²
  have h_gap : 1 - (k * T / (k * T + 1))^2 = (2 * (k * T) + 1) / (k * T + 1)^2 := by
    field_simp; ring
  rw [h_gap]
  -- (2kT+1)/(kT+1)² ≤ 3/(kT)
  -- ⟺ (2kT+1)·kT ≤ 3·(kT+1)²
  -- ⟺ 2(kT)² + kT ≤ 3(kT)² + 6kT + 3
  -- ⟺ 0 ≤ (kT)² + 5kT + 3 ✓
  rw [div_le_div_iff₀ (sq_pos_of_pos hden) hkT]
  nlinarith [sq_nonneg (k * T)]

/-- Implied variance of scaledStep vanishes as k → ∞. -/
theorem implied_variance_vanishes
    (p₀ n₀ sB sC : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
    |(scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).toScalar.impliedVariance| < ε := by
  intro ε hε
  have hT : 0 < p₀ + n₀ := by linarith
  -- |impliedVar| = |s(1-s)| · (1-c_h) where s is constant
  -- and (1-c_h) ≤ 3/(k·T₀).
  -- So |impliedVar| ≤ |s(1-s)| · 3/(k·T₀).
  -- For k ≥ ⌈3·|s(1-s)| / (ε·T₀)⌉ + 1, this is < ε.

  -- Get the constant output strength (use k=1 as reference)
  set s₀ := (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 1 (by norm_num)).toScalar.outputStrength
  set M := |s₀ * (1 - s₀)| + 1 -- ensure M > 0
  have hM_pos : 0 < M := by positivity
  use Nat.ceil (3 * M / (ε * (p₀ + n₀))) + 1
  intro k hk hk_pos
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos

  -- Output strength is constant
  have hs_const : (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk_pos).toScalar.outputStrength = s₀ :=
    scaledStep_outputStrength_const p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k 1 hk_pos (by norm_num)

  -- Use the implied variance identity
  set step := scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk_pos
  have hc_lt := scaledStep_hc_lt_one p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk_pos
  rw [impliedVariance_eq step.toScalar hc_lt, hs_const]

  -- |s₀(1-s₀)(1-c_h)| = |s₀(1-s₀)| · |1-c_h| = |s₀(1-s₀)| · (1-c_h)
  -- since 1-c_h > 0
  have hgap_nn : 0 ≤ 1 - step.toScalar.heuristicConfidence := by linarith
  rw [abs_mul, abs_of_nonneg hgap_nn]

  -- Bound 1 - c_h
  have hgap_le := scaledStep_confidence_gap_le p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk_pos

  calc |s₀ * (1 - s₀)| * (1 - step.toScalar.heuristicConfidence)
      ≤ |s₀ * (1 - s₀)| * (3 / (k * (p₀ + n₀))) :=
        mul_le_mul_of_nonneg_left hgap_le (abs_nonneg _)
    _ ≤ M * (3 / (k * (p₀ + n₀))) := by
        apply mul_le_mul_of_nonneg_right _ (div_nonneg (by norm_num) (by positivity))
        linarith [abs_nonneg (s₀ * (1 - s₀))]
    _ = 3 * M / (k * (p₀ + n₀)) := by ring
    _ < ε := by
        rw [div_lt_iff₀ (mul_pos hk' hT)]
        have h1 : (↑(Nat.ceil (3 * M / (ε * (p₀ + n₀))) + 1) : ℝ) ≤ k :=
          Nat.cast_le.mpr hk
        have h2 : 3 * M / (ε * (p₀ + n₀)) ≤ ↑(Nat.ceil (3 * M / (ε * (p₀ + n₀)))) :=
          Nat.le_ceil _
        push_cast at h1
        have h3 : 3 * M ≤ ε * (↑(Nat.ceil (3 * M / (ε * (p₀ + n₀)))) * (p₀ + n₀)) := by
          have := (div_le_iff₀ (mul_pos hε hT)).mp (le_trans (le_refl _) h2)
          nlinarith
        nlinarith

/-! ## Step 5: Exact Variance Vanishes for ScaledStep -/

/-- Exact variance of scaledStep vanishes as k → ∞. -/
theorem exact_variance_vanishes
    (p₀ n₀ sB sC : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
    (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).exactVariance < ε := by
  intro ε hε
  have hB : sB ≠ 1 := ne_of_lt hsB1
  obtain ⟨δ, hδ, hbound⟩ := exact_variance_vanishes_of_input_variance
    (p₀ / (p₀ + n₀)) (p₀ / (p₀ + n₀)) sB sC hB ε hε
  obtain ⟨N, hN⟩ := beta_variance_vanishes p₀ n₀ hp hn δ hδ
  use N
  intro k hk hk_pos
  have hvar := hN k hk hk_pos
  simp only [scaledStep, DistributionalChainStep.exactVariance]
  have hvar_nn := le_of_lt (scaledEvidence p₀ n₀ hp hn k hk_pos).variance_pos
  have hs_eq := scaledEvidence_strength p₀ n₀ hp hn k hk_pos
  rw [hs_eq]
  exact hbound _ _ hvar_nn hvar_nn hvar hvar

/-! ## Step 6: Approximation Error Vanishes -/

/-- The approximation error vanishes as evidence grows. -/
theorem approximation_error_vanishes
    (p₀ n₀ sB sC : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
    |varianceApproximationError
      (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk)| < ε := by
  intro ε hε
  -- |error| = |implied - exact| ≤ |implied| + |exact|
  -- Get N₁ for |implied| < ε/2
  obtain ⟨N₁, hN₁⟩ := implied_variance_vanishes p₀ n₀ sB sC hp hn hsB hsB1 hsC0 hsC1
    (ε/2) (by linarith)
  -- Get N₂ for exact < ε/2
  obtain ⟨N₂, hN₂⟩ := exact_variance_vanishes p₀ n₀ sB sC hp hn hsB hsB1 hsC0 hsC1
    (ε/2) (by linarith)
  use max N₁ N₂
  intro k hk hk_pos
  set step := scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk_pos

  have h_implied := hN₁ k (le_trans (le_max_left _ _) hk) hk_pos
  have h_exact := hN₂ k (le_trans (le_max_right _ _) hk) hk_pos

  -- exact variance ≥ 0
  have h_exact_nn : 0 ≤ step.exactVariance := by
    unfold DistributionalChainStep.exactVariance trueFullDeductionVariance
    exact varianceAffineProductIndep_nonneg _ _ _ _ _ _ _
      (le_of_lt step.evidence_AB.variance_pos)
      (le_of_lt step.evidence_BC.variance_pos)

  unfold varianceApproximationError
  have h_abs_le : |step.toScalar.impliedVariance - step.exactVariance| ≤
      |step.toScalar.impliedVariance| + step.exactVariance := by
    set iv := step.toScalar.impliedVariance
    set ev := step.exactVariance
    calc |iv - ev| = |iv + (-ev)| := by rw [sub_eq_add_neg]
      _ ≤ |iv| + |-ev| := abs_add_le iv (-ev)
      _ = |iv| + ev := by rw [abs_neg, abs_of_nonneg h_exact_nn]
  linarith

/-! ## Step 7: Summary Theorem -/

/-- **Summary Theorem**: Scalar inference converges to distributional
    inference in the high-evidence limit.

    For any fixed base evidence (p₀, n₀) and deduction parameters (sB, sC),
    scaling evidence by k → ∞ causes:
    1. The exact deduction variance to vanish (→ 0)
    2. The heuristic-implied variance to vanish (→ 0)
    3. The approximation error between them to vanish (→ 0)

    Combined with `distributional_dominates_scalar` (which shows the error
    is nonzero for finite evidence), this establishes:
    - Scalar inference is asymptotically correct but wrong in the middle.
    - Distributional inference (PLN book Ch. 6) is exact everywhere. -/
theorem scalar_converges_to_distributional
    (p₀ n₀ sB sC : ℝ) (hp : 0 < p₀) (hn : 0 < n₀)
    (hsB : 0 < sB) (hsB1 : sB < 1)
    (hsC0 : 0 ≤ sC) (hsC1 : sC ≤ 1) :
    -- Exact variance vanishes
    (∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
      (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).exactVariance < ε) ∧
    -- Implied variance vanishes
    (∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
      |(scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk).toScalar.impliedVariance| < ε) ∧
    -- Approximation error vanishes
    (∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (hk : 0 < k) →
      |varianceApproximationError
        (scaledStep p₀ n₀ hp hn sB sC hsB hsB1 hsC0 hsC1 k hk)| < ε) :=
  ⟨exact_variance_vanishes p₀ n₀ sB sC hp hn hsB hsB1 hsC0 hsC1,
   implied_variance_vanishes p₀ n₀ sB sC hp hn hsB hsB1 hsC0 hsC1,
   approximation_error_vanishes p₀ n₀ sB sC hp hn hsB hsB1 hsC0 hsC1⟩

end Mettapedia.Logic.PLN.DistributionalConvergence
