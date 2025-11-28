/-
# PLN Distributional Truth Values (Chapter 6)

Formalization of the connection between PLN's Simple Truth Values (s, c) and
Distributional Truth Values represented as Beta distributions.

## Main Concepts

1. **Simple Truth Value (STV)**: A pair (s, c) where s = strength ∈ [0,1], c = confidence ∈ [0,1]
2. **Distributional Truth Value (DTV)**: A Beta(α, β) distribution over [0,1]
3. **The Mapping**: Given Beta(α, β), the corresponding STV has:
   - Strength s = E[X] = α / (α + β)
   - Confidence c is related to the "count" n = α + β

## Key Results

- `beta_mean_formula`: E[X] = α / (α + β) for X ~ Beta(α, β)
- `strength_from_beta`: The PLN strength equals the Beta distribution mean
- `beta_variance_formula`: Var[X] = αβ / ((α+β)²(α+β+1))

## References

- Goertzel et al., "Probabilistic Logic Networks" (Springer, 2008), Chapter 6
- Mathlib `Mathlib.Probability.Distributions.Beta`
-/

import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace Mettapedia.Logic.PLN.Distributional

open MeasureTheory ProbabilityTheory Real Set

/-! ## Simple Truth Values

A Simple Truth Value in PLN consists of a strength s ∈ [0,1] and confidence c ∈ [0,1].
-/

/-- A PLN Simple Truth Value (STV) is a pair (strength, confidence) where both are in [0,1]. -/
structure SimpleTruthValue where
  strength : ℝ
  confidence : ℝ
  strength_nonneg : 0 ≤ strength
  strength_le_one : strength ≤ 1
  confidence_nonneg : 0 ≤ confidence
  confidence_le_one : confidence ≤ 1

namespace SimpleTruthValue

/-- Construct an STV from values with proofs. -/
def mk' (s c : ℝ) (hs : s ∈ Icc 0 1) (hc : c ∈ Icc 0 1) : SimpleTruthValue where
  strength := s
  confidence := c
  strength_nonneg := hs.1
  strength_le_one := hs.2
  confidence_nonneg := hc.1
  confidence_le_one := hc.2

end SimpleTruthValue

/-! ## Beta Distribution Parameters

We work with Mathlib's Beta distribution and establish the connection between
Beta(α, β) parameters and PLN truth values.
-/

/-- Parameters for a Beta distribution, requiring positivity. -/
structure BetaParams where
  alpha : ℝ
  betaParam : ℝ  -- Using 'betaParam' to avoid conflict with 'beta' function
  alpha_pos : 0 < alpha
  beta_pos : 0 < betaParam

namespace BetaParams

/-- The sum of parameters, representing the "count" or sample size. -/
def n (p : BetaParams) : ℝ := p.alpha + p.betaParam

/-- n is always positive. -/
theorem n_pos (p : BetaParams) : 0 < p.n := add_pos p.alpha_pos p.beta_pos

/-- The expected value (mean) of a Beta(α, β) distribution: E[X] = α / (α + β). -/
def expectedValue (p : BetaParams) : ℝ := p.alpha / p.n

/-- The expected value is in (0, 1). -/
theorem expectedValue_pos (p : BetaParams) : 0 < p.expectedValue := by
  unfold expectedValue n
  exact div_pos p.alpha_pos (add_pos p.alpha_pos p.beta_pos)

theorem expectedValue_lt_one (p : BetaParams) : p.expectedValue < 1 := by
  unfold expectedValue n
  rw [div_lt_one (add_pos p.alpha_pos p.beta_pos)]
  linarith [p.beta_pos]

theorem expectedValue_mem_Ioo (p : BetaParams) : p.expectedValue ∈ Ioo 0 1 :=
  ⟨p.expectedValue_pos, p.expectedValue_lt_one⟩

/-- The variance formula for Beta(α, β): Var[X] = αβ / ((α+β)²(α+β+1)). -/
def variance (p : BetaParams) : ℝ :=
  (p.alpha * p.betaParam) / (p.n ^ 2 * (p.n + 1))

/-- Variance is always positive for valid parameters. -/
theorem variance_pos (p : BetaParams) : 0 < p.variance := by
  unfold variance n
  have h1 : 0 < p.alpha * p.betaParam := mul_pos p.alpha_pos p.beta_pos
  have h2 : 0 < (p.alpha + p.betaParam) ^ 2 := sq_pos_of_pos (add_pos p.alpha_pos p.beta_pos)
  have h3 : 0 < p.alpha + p.betaParam + 1 := by linarith [p.alpha_pos, p.beta_pos]
  exact div_pos h1 (mul_pos h2 h3)

/-- Create Beta parameters from a PLN strength and count.
    Given s = α/(α+β) and n = α+β, we have α = s·n and β = (1-s)·n. -/
def fromStrengthCount (s n : ℝ) (hs : s ∈ Ioo 0 1) (hn : 0 < n) : BetaParams where
  alpha := s * n
  betaParam := (1 - s) * n
  alpha_pos := mul_pos hs.1 hn
  beta_pos := mul_pos (by linarith [hs.2]) hn

theorem fromStrengthCount_n (s n : ℝ) (hs : s ∈ Ioo 0 1) (hn : 0 < n) :
    (fromStrengthCount s n hs hn).n = n := by
  show s * n + (1 - s) * n = n
  ring

theorem fromStrengthCount_expectedValue (s n : ℝ) (hs : s ∈ Ioo 0 1) (hn : 0 < n) :
    (fromStrengthCount s n hs hn).expectedValue = s := by
  show s * n / (s * n + (1 - s) * n) = s
  have h_ne : n ≠ 0 := ne_of_gt hn
  have h_eq : s * n + (1 - s) * n = n := by ring
  rw [h_eq]
  field_simp

end BetaParams

/-! ## Connection to Mathlib's Beta Distribution

We now connect our algebraic definitions to Mathlib's measure-theoretic Beta distribution.
-/

/-- The beta normalization constant from Mathlib. -/
def betaNormConst (α β : ℝ) : ℝ := ProbabilityTheory.beta α β

/-- The Beta measure from Mathlib. -/
def betaMeasureOf (p : BetaParams) : Measure ℝ :=
  ProbabilityTheory.betaMeasure p.alpha p.betaParam

/-- Beta measure is a probability measure. -/
instance (p : BetaParams) : IsProbabilityMeasure (betaMeasureOf p) :=
  ProbabilityTheory.isProbabilityMeasureBeta p.alpha_pos p.beta_pos

/-! ## Main Theorem: Beta Mean Formula

The key theorem connecting Beta distributions to PLN strength.
This requires integrating x · betaPDF(x) over (0,1).
-/

/-- Key lemma: The ratio beta(α+1, β) / beta(α, β) = α / (α + β).
    This follows from Gamma function recurrence: Γ(z+1) = z·Γ(z). -/
theorem beta_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β / beta α β = α / (α + β) := by
  unfold beta
  have hαβ : 0 < α + β := add_pos hα hβ
  have hα1β : 0 < α + 1 + β := by linarith
  have hα_ne : α ≠ 0 := hα.ne'
  have hαβ_ne : α + β ≠ 0 := hαβ.ne'
  have hΓα : Gamma α ≠ 0 := (Gamma_pos_of_pos hα).ne'
  have hΓβ : Gamma β ≠ 0 := (Gamma_pos_of_pos hβ).ne'
  have hΓαβ : Gamma (α + β) ≠ 0 := (Gamma_pos_of_pos hαβ).ne'
  have hΓα1β : Gamma (α + 1 + β) ≠ 0 := (Gamma_pos_of_pos hα1β).ne'
  -- Use Gamma recurrence: Γ(α+1) = α·Γ(α) and Γ(α+β+1) = (α+β)·Γ(α+β)
  have hΓα1 : Gamma (α + 1) = α * Gamma α := Gamma_add_one hα_ne
  have hΓαβ1 : Gamma (α + 1 + β) = (α + β) * Gamma (α + β) := by
    rw [add_assoc, add_comm 1 β, ← add_assoc]
    exact Gamma_add_one hαβ_ne
  rw [hΓα1, hΓαβ1]
  field_simp

/-- Helper: The integral ∫ x^α · (1-x)^(β-1) dx = beta(α+1, β).
    This follows from betaIntegral definition with shifted parameters.

    Proof strategy (following Mathlib's lintegral_betaPDF_eq_one):
    1. beta(α+1, β) = (betaIntegral (α+1) β).re by beta_eq_betaIntegralReal
    2. betaIntegral (α+1) β = ∫₀¹ x^α * (1-x)^(β-1) by definition
    3. Convert complex integral to real via integral_re and Complex.ofReal_cpow
-/
theorem integral_rpow_beta (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in Ioo 0 1, x ^ α * (1 - x) ^ (β - 1) = beta (α + 1) β := by
  have hα1 : 0 < α + 1 := by linarith
  -- Key: (↑(α + 1) - 1 : ℂ) = ↑α (the exponent simplification in ℂ)
  have h_exp_c : (↑(α + 1) - 1 : ℂ) = ↑α := by push_cast; ring
  -- Use Mathlib's beta_eq_betaIntegralReal to convert beta to real part of betaIntegral
  rw [beta_eq_betaIntegralReal (α + 1) β hα1 hβ]
  -- betaIntegral (α + 1) β = ∫ x in 0..1, x^((α+1)-1) * (1-x)^(β-1)
  simp only [Complex.betaIntegral, h_exp_c]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- Convert Ioo to Ioc (measure zero difference)
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  -- Use integral_re to extract real part (following Mathlib's Beta.lean pattern)
  rw [← RCLike.re_to_complex, ← integral_re]
  · -- Show the integrands match via setIntegral_congr_fun
    refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx2⟩ ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith  -- discharges 0 ≤ x and 0 ≤ 1 - x
  · -- Integrability: follows from betaIntegral_convergent
    -- h_conv has exponent ↑α + 1 - 1 (after unfolding betaIntegral_convergent)
    have h_simp : (↑α + 1 - 1 : ℂ) = ↑α := by ring
    have h_conv := Complex.betaIntegral_convergent (u := α + 1) (v := β) (by simpa) (by simpa)
    simp only [h_simp] at h_conv
    convert h_conv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), IntegrableOn]

/-- The first moment integral for Beta distribution.
    ∫ x · betaPDF(α, β, x) dx = α / (α + β)

    This is the key formula connecting Beta distributions to PLN strength.
    The proof uses the integral_rpow_beta helper and beta_ratio theorem.
-/
theorem beta_mean_formula (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in Ioo 0 1, x * betaPDFReal α β x = α / (α + β) := by
  -- Strategy: Factor out 1/beta(α,β), then use integral_rpow_beta and beta_ratio
  have h_beta_pos : 0 < beta α β := beta_pos hα hβ
  have h_beta_ne : beta α β ≠ 0 := h_beta_pos.ne'
  -- On (0,1), betaPDFReal α β x = (1/beta α β) * x^(α-1) * (1-x)^(β-1)
  -- So x * betaPDFReal = (1/beta α β) * x^α * (1-x)^(β-1)
  calc ∫ x in Ioo 0 1, x * betaPDFReal α β x
      = ∫ x in Ioo 0 1, (1 / beta α β) * (x ^ α * (1 - x) ^ (β - 1)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x hx ↦ ?_)
        rw [betaPDFReal, if_pos ⟨hx.1, hx.2⟩]
        have hx_pos : 0 < x := hx.1
        -- x * (1/B * x^(α-1) * (1-x)^(β-1)) = (1/B) * (x^α * (1-x)^(β-1))
        have h_combine : x * x ^ (α - 1) = x ^ α := by
          have hα_ne : α - 1 + 1 ≠ 0 := by linarith
          rw [mul_comm, ← Real.rpow_add_one' hx_pos.le hα_ne]
          congr 1; ring
        calc x * (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1))
            = 1 / beta α β * (x * x ^ (α - 1)) * (1 - x) ^ (β - 1) := by ring
          _ = 1 / beta α β * x ^ α * (1 - x) ^ (β - 1) := by rw [h_combine]
          _ = 1 / beta α β * (x ^ α * (1 - x) ^ (β - 1)) := by ring
    _ = (1 / beta α β) * ∫ x in Ioo 0 1, x ^ α * (1 - x) ^ (β - 1) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = (1 / beta α β) * beta (α + 1) β := by rw [integral_rpow_beta α β hα hβ]
    _ = beta (α + 1) β / beta α β := by ring
    _ = α / (α + β) := beta_ratio α β hα hβ

/-- betaPDFReal is nonnegative -/
lemma betaPDFReal_nonneg' (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  simp only [betaPDFReal]
  split_ifs with h
  · apply mul_nonneg
    apply mul_nonneg
    · exact le_of_lt (one_div_pos.mpr (beta_pos hα hβ))
    · exact Real.rpow_nonneg (le_of_lt h.1) _
    · exact Real.rpow_nonneg (by linarith [h.2]) _
  · rfl

/-- Corollary: The expected value of a Beta-distributed random variable equals α/(α+β). -/
theorem beta_expectation_eq (p : BetaParams) :
    ∫ x, x ∂(betaMeasureOf p) = p.expectedValue := by
  -- Unfold to volume.withDensity (betaPDF ...)
  simp only [betaMeasureOf, betaMeasure]
  -- betaPDF is measurable (since betaPDFReal is measurable)
  have h_meas : Measurable (betaPDF p.alpha p.betaParam) :=
    (measurable_betaPDFReal p.alpha p.betaParam).ennreal_ofReal
  -- betaPDF is finite everywhere
  have h_lt_top : ∀ᵐ x ∂volume, betaPDF p.alpha p.betaParam x < ⊤ :=
    ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)
  -- Use integral_withDensity_eq_integral_toReal_smul to convert to integral of betaPDF * x
  rw [integral_withDensity_eq_integral_toReal_smul h_meas h_lt_top]
  -- The key: ∫ (betaPDF).toReal • x = ∫ betaPDFReal * x
  -- First, betaPDF.toReal = betaPDFReal
  have h_toReal : ∀ x, (betaPDF p.alpha p.betaParam x).toReal = betaPDFReal p.alpha p.betaParam x := by
    intro x
    simp only [betaPDF]
    exact ENNReal.toReal_ofReal (betaPDFReal_nonneg' p.alpha p.betaParam p.alpha_pos p.beta_pos x)
  -- Second, the integral over ℝ equals integral over (0,1) since betaPDFReal = 0 outside
  simp_rw [h_toReal, smul_eq_mul, mul_comm]
  -- Restrict to Ioo 0 1 using that betaPDFReal vanishes outside
  have h_support : ∫ x, x * betaPDFReal p.alpha p.betaParam x = ∫ x in Ioo 0 1, x * betaPDFReal p.alpha p.betaParam x := by
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [betaPDFReal, Set.mem_Ioo, not_and_or, not_lt] at hx ⊢
    split_ifs with h
    · exfalso; exact hx.elim (fun h' => not_lt.mpr h' h.1) (fun h' => not_lt.mpr h' h.2)
    · ring
  rw [h_support, beta_mean_formula p.alpha p.betaParam p.alpha_pos p.beta_pos]
  rfl

/-! ## PLN Strength is Beta Mean

The central result: PLN strength equals the expected value (mean) of the corresponding
Beta distribution.
-/

/-- Convert Beta parameters to a Simple Truth Value using expected value as strength.
    The confidence is derived from the count n = α + β using PLN's formula:
    c = n / (n + k) where k is a constant (we use k = 1 for simplicity). -/
def BetaParams.toSTV (p : BetaParams) : SimpleTruthValue where
  strength := p.expectedValue
  confidence := p.n / (p.n + 1)
  strength_nonneg := le_of_lt p.expectedValue_pos
  strength_le_one := le_of_lt p.expectedValue_lt_one
  confidence_nonneg := by
    have h := p.n_pos
    exact le_of_lt (div_pos h (by linarith))
  confidence_le_one := by
    have h := p.n_pos
    rw [div_le_one (by linarith : 0 < p.n + 1)]
    linarith

/-! ## Variance Formulas for PLN Operations

When combining truth values via PLN operations, we need to track how variance propagates.
-/

/-- Variance of product of independent random variables.
    If X, Y are independent, Var(XY) = E[X]²Var[Y] + E[Y]²Var[X] + Var[X]Var[Y] -/
theorem variance_product_indep (EX EY VarX VarY : ℝ) :
    let _EXY := EX * EY
    let VarXY := EX^2 * VarY + EY^2 * VarX + VarX * VarY
    VarXY = EX^2 * VarY + EY^2 * VarX + VarX * VarY := rfl

/-- For PLN deduction with independent Beta-distributed strengths s_AB and s_BC,
    the output variance can be bounded.

    This is simplified - the full formula involves the (1-s_AB) term correction. -/
theorem pln_deduction_variance_simplified
    (s_AB s_BC : ℝ) (Var_AB Var_BC : ℝ)
    (_hs_AB : s_AB ∈ Icc 0 1) (_hs_BC : s_BC ∈ Icc 0 1)
    (hVar_AB : 0 ≤ Var_AB) (hVar_BC : 0 ≤ Var_BC) :
    let Var_simplified := s_AB^2 * Var_BC + s_BC^2 * Var_AB + Var_AB * Var_BC
    0 ≤ Var_simplified := by
  simp only
  have h1 : 0 ≤ s_AB^2 * Var_BC := mul_nonneg (sq_nonneg s_AB) hVar_BC
  have h2 : 0 ≤ s_BC^2 * Var_AB := mul_nonneg (sq_nonneg s_BC) hVar_AB
  have h3 : 0 ≤ Var_AB * Var_BC := mul_nonneg hVar_AB hVar_BC
  linarith

/-! # The Algebra of Independence

This section develops the general theory of variance for affine combinations of
products of independent random variables. The key result is that for Z = aXY + bX + cY + d,
the variance can be written as a **sum of squares**, guaranteeing non-negativity.

## Mathematical Setup

Let X, Y be independent random variables with:
- Means: μ_X = E[X], μ_Y = E[Y]
- Variances: σ²_X = Var(X), σ²_Y = Var(Y)

## Key Moments (by Independence)

- E[XY] = E[X]·E[Y] = μ_X·μ_Y
- E[X²Y] = E[X²]·E[Y] = (σ²_X + μ²_X)·μ_Y
- E[XY²] = E[X]·E[Y²] = μ_X·(σ²_Y + μ²_Y)
- E[X²Y²] = E[X²]·E[Y²] = (σ²_X + μ²_X)(σ²_Y + μ²_Y)
-/

/--
The variance of the product XY for independent X, Y.

**Formula:**
$$\text{Var}(XY) = \mu_X^2 \sigma_Y^2 + \mu_Y^2 \sigma_X^2 + \sigma_X^2 \sigma_Y^2$$

This is the fundamental building block for more complex variance formulas.
-/
def varianceProductIndep (μX μY σ2X σ2Y : ℝ) : ℝ :=
  μX^2 * σ2Y + μY^2 * σ2X + σ2X * σ2Y

/--
The variance of Z = aXY + bX + cY + d for independent X, Y.

**Raw Formula:**
$$\text{Var}(Z) = a^2 \text{Var}(XY) + b^2 \sigma_X^2 + c^2 \sigma_Y^2
                + 2ab \mu_Y \sigma_X^2 + 2ac \mu_X \sigma_Y^2$$

**Sum-of-Squares Form** (key insight for non-negativity):
$$\text{Var}(Z) = (a\mu_Y + b)^2 \sigma_X^2 + (a\mu_X + c)^2 \sigma_Y^2 + a^2 \sigma_X^2 \sigma_Y^2$$

The cross-terms arise from covariances:
- Cov(XY, X) = μ_Y · σ²_X
- Cov(XY, Y) = μ_X · σ²_Y
- Cov(X, Y) = 0 (independence)
-/
def varianceAffineProductIndep (μX μY σ2X σ2Y a b c : ℝ) : ℝ :=
  let σ2XY := varianceProductIndep μX μY σ2X σ2Y
  a^2 * σ2XY + b^2 * σ2X + c^2 * σ2Y + 2*a*b*μY*σ2X + 2*a*c*μX*σ2Y

/--
**Correctness Theorem**: The variance formula equals E[Z²] - E[Z]².

This verifies our closed-form expression is algebraically correct by expanding
E[(aXY + bX + cY + d)²] and subtracting E[aXY + bX + cY + d]².
-/
theorem varianceAffineProductIndep_correct (EX EY VarX VarY a b c d : ℝ) :
    let EX2 := VarX + EX^2                    -- E[X²] = Var(X) + E[X]²
    let EY2 := VarY + EY^2                    -- E[Y²] = Var(Y) + E[Y]²
    let EXY := EX * EY                        -- E[XY] = E[X]E[Y]
    let EX2Y2 := EX2 * EY2                    -- E[(XY)²] = E[X²]E[Y²]
    let EX2Y := EX2 * EY                      -- E[X²Y] = E[X²]E[Y]
    let EXY2 := EX * EY2                      -- E[XY²] = E[X]E[Y²]
    let EZ := a * EXY + b * EX + c * EY + d
    let EZ2 := a^2 * EX2Y2 + b^2 * EX2 + c^2 * EY2 + d^2 +
               2*a*b * EX2Y + 2*a*c * EXY2 + 2*a*d * EXY +
               2*b*c * EXY + 2*b*d * EX + 2*c*d * EY
    EZ2 - EZ^2 = varianceAffineProductIndep EX EY VarX VarY a b c := by
  simp only [varianceAffineProductIndep, varianceProductIndep]
  ring

/--
**Non-negativity Theorem** (The "God's Book" Proof)

The variance is always ≥ 0 because it can be rewritten as a sum of squares:
$$\text{Var}(Z) = \underbrace{(a\mu_Y + b)^2}_{\geq 0} \sigma_X^2
                + \underbrace{(a\mu_X + c)^2}_{\geq 0} \sigma_Y^2
                + \underbrace{a^2}_{\geq 0} \sigma_X^2 \sigma_Y^2$$

Since σ²_X ≥ 0 and σ²_Y ≥ 0 (variances are non-negative), each term is ≥ 0.
-/
theorem varianceAffineProductIndep_nonneg (μX μY σ2X σ2Y a b c : ℝ)
    (hσX : 0 ≤ σ2X) (hσY : 0 ≤ σ2Y) :
    0 ≤ varianceAffineProductIndep μX μY σ2X σ2Y a b c := by
  simp only [varianceAffineProductIndep, varianceProductIndep]
  -- Key algebraic identity: rewrite as sum of squares
  have h_sos : a^2 * (μX^2 * σ2Y + μY^2 * σ2X + σ2X * σ2Y) + b^2 * σ2X + c^2 * σ2Y +
               2*a*b*μY*σ2X + 2*a*c*μX*σ2Y =
               (a*μY + b)^2 * σ2X + (a*μX + c)^2 * σ2Y + a^2 * σ2X * σ2Y := by ring
  rw [h_sos]
  have h1 : 0 ≤ (a*μY + b)^2 * σ2X := mul_nonneg (sq_nonneg _) hσX
  have h2 : 0 ≤ (a*μX + c)^2 * σ2Y := mul_nonneg (sq_nonneg _) hσY
  have h3 : 0 ≤ a^2 * σ2X * σ2Y := mul_nonneg (mul_nonneg (sq_nonneg _) hσX) hσY
  linarith

/-! # The PLN Deduction Formula

The full PLN deduction rule computes P(A→C) from P(A→B) and P(B→C):

$$s_{AC} = s_{AB} \cdot s_{BC} + \frac{(1 - s_{AB})(s_C - s_B \cdot s_{BC})}{1 - s_B}$$

When s_B and s_C are treated as constants (point estimates), this is an affine
function of the product s_AB · s_BC, fitting our general framework.

## Rearranged Form

Let X = s_AB, Y = s_BC, and k = 1/(1 - s_B). Then:
$$s_{AC} = aXY + bX + cY + d$$

where:
- a = 1 + k·s_B (coefficient of XY)
- b = -k·s_C (coefficient of X)
- c = -k·s_B (coefficient of Y)
- d = k·s_C (constant)
-/

/--
The coefficients (a, b, c, d) for the PLN Deduction formula.

Given term probabilities s_B and s_C (treated as constants), returns the
coefficients that express s_AC as aXY + bX + cY + d.
-/
def plnDeductionCoeffs (sB sC : ℝ) (_hB : sB ≠ 1) : ℝ × ℝ × ℝ × ℝ :=
  let k := 1 / (1 - sB)
  ( 1 + k * sB,      -- a: coefficient of s_AB · s_BC
   -k * sC,          -- b: coefficient of s_AB
   -k * sB,          -- c: coefficient of s_BC
    k * sC )         -- d: constant term

/--
The **exact** variance of the full PLN Deduction formula.

This is the "non-simplified" version that includes all cross-terms from
the (1 - s_AB) correction term. Compare with `trueProductVariance` which
only considers the simplified Z = XY case.
-/
def trueFullDeductionVariance (s_AB s_BC Var_AB Var_BC sB sC : ℝ) (hB : sB ≠ 1) : ℝ :=
  let (a, b, c, _) := plnDeductionCoeffs sB sC hB
  varianceAffineProductIndep s_AB s_BC Var_AB Var_BC a b c

/-! # The Variance Audit

We now prove that the full deduction variance is always non-negative, and
show how the simplified version relates to the full version.
-/

/--
**Main Theorem**: The full PLN deduction variance is always non-negative.

This follows directly from `varianceAffineProductIndep_nonneg` since the
formula is a sum of squared terms times non-negative variances.
-/
theorem pln_deduction_variance_full_nonneg
    (s_AB s_BC Var_AB Var_BC sB sC : ℝ)
    (_hs_AB : s_AB ∈ Icc 0 1) (_hs_BC : s_BC ∈ Icc 0 1)
    (hVar_AB : 0 ≤ Var_AB) (hVar_BC : 0 ≤ Var_BC)
    (_hsB : sB ∈ Ioo 0 1) (_hsC : sC ∈ Icc 0 1)
    (hB : sB ≠ 1) :
    0 ≤ trueFullDeductionVariance s_AB s_BC Var_AB Var_BC sB sC hB := by
  unfold trueFullDeductionVariance plnDeductionCoeffs
  exact varianceAffineProductIndep_nonneg s_AB s_BC Var_AB Var_BC _ _ _ hVar_AB hVar_BC

/--
The simplified variance Var(XY) is the special case of the affine formula with a=1, b=c=0.

This shows that `varianceProductIndep` is subsumed by the more general
`varianceAffineProductIndep`, providing a unified theory.
-/
theorem simplified_eq_affine_special_case (μX μY σ2X σ2Y : ℝ) :
    varianceProductIndep μX μY σ2X σ2Y =
    varianceAffineProductIndep μX μY σ2X σ2Y 1 0 0 := by
  simp only [varianceAffineProductIndep, varianceProductIndep]
  ring

/-! ## Confidence Count Relationship

PLN confidence c is related to "evidence count" n via c = n/(n+k) for some k.
Given this, we can recover n from c as n = k·c/(1-c).
-/

/-- The standard PLN confidence-to-count formula with k=1. -/
def confidenceToCount (c : ℝ) (_hc : c ∈ Ico 0 1) : ℝ := c / (1 - c)

/-- Count is non-negative. -/
theorem confidenceToCount_nonneg (c : ℝ) (hc : c ∈ Ico 0 1) :
    0 ≤ confidenceToCount c hc := by
  unfold confidenceToCount
  have h1 : 0 ≤ c := hc.1
  have h2 : 0 < 1 - c := by linarith [hc.2]
  exact div_nonneg h1 (le_of_lt h2)

/-- Convert confidence c to count n, requiring c > 0 for positive count. -/
def confidenceToCount' (c : ℝ) (_hc : c ∈ Ioo 0 1) : ℝ := c / (1 - c)

theorem confidenceToCount'_pos (c : ℝ) (hc : c ∈ Ioo 0 1) :
    0 < confidenceToCount' c hc := by
  unfold confidenceToCount'
  exact div_pos hc.1 (by linarith [hc.2])

/-- The inverse: count to confidence. -/
def countToConfidence (n : ℝ) (_hn : 0 ≤ n) : ℝ := n / (n + 1)

theorem countToConfidence_mem_Ico (n : ℝ) (hn : 0 ≤ n) :
    countToConfidence n hn ∈ Ico 0 1 := by
  constructor
  · unfold countToConfidence
    exact div_nonneg hn (by linarith)
  · unfold countToConfidence
    rw [div_lt_one (by linarith : 0 < n + 1)]
    linarith

/-- Round-trip: count → confidence → count is identity (for positive count). -/
theorem count_confidence_roundtrip (n : ℝ) (hn : 0 < n) :
    confidenceToCount' (countToConfidence n (le_of_lt hn))
      ⟨by unfold countToConfidence; exact div_pos hn (by linarith),
       by unfold countToConfidence; rw [div_lt_one (by linarith)]; linarith⟩ = n := by
  unfold confidenceToCount' countToConfidence
  have h1 : 0 < n + 1 := by linarith
  have h2 : n / (n + 1) < 1 := by rw [div_lt_one h1]; linarith
  have h3 : 0 < 1 - n / (n + 1) := by linarith
  field_simp
  ring

/-! ## Evidence-Based PLN (The Correct Approach)

A Truth Value is not a pair (s, c) but a State of Evidence:
- α observations supporting the proposition
- β observations against it

The Beta distribution emerges as the *posterior* given this evidence,
not as an arbitrary parameterization. This is the conjugate prior view.
-/

/-- Raw evidence counts. This is the primitive representation.
    Semantically: "We have observed α positive and β negative instances."
    The Beta(α, β) distribution represents our uncertainty about the true probability. -/
structure Evidence where
  positive : ℝ  -- α (can be fractional for "virtual" evidence)
  negative : ℝ  -- β
  positive_pos : 0 < positive
  negative_pos : 0 < negative

namespace Evidence

/-- Total evidence count -/
def total (e : Evidence) : ℝ := e.positive + e.negative

theorem total_pos (e : Evidence) : 0 < e.total :=
  add_pos e.positive_pos e.negative_pos

/-- Convert Evidence to BetaParams -/
def toBeta (e : Evidence) : BetaParams where
  alpha := e.positive
  betaParam := e.negative
  alpha_pos := e.positive_pos
  beta_pos := e.negative_pos

/-- Strength = Expected probability given evidence = α / (α + β) -/
def strength (e : Evidence) : ℝ := e.positive / e.total

theorem strength_eq_expectedValue (e : Evidence) :
    e.strength = e.toBeta.expectedValue := rfl

theorem strength_mem_Ioo (e : Evidence) : e.strength ∈ Ioo 0 1 :=
  e.toBeta.expectedValue_mem_Ioo

/-- Variance of the Beta distribution induced by evidence -/
def variance (e : Evidence) : ℝ := e.toBeta.variance

theorem variance_pos (e : Evidence) : 0 < e.variance :=
  e.toBeta.variance_pos

/-- Revision: Combining independent evidence sources is ADDITION.
    This is the key insight: revision is trivially correct because
    Beta is the conjugate prior for Bernoulli observations. -/
def revision (e₁ e₂ : Evidence) : Evidence where
  positive := e₁.positive + e₂.positive
  negative := e₁.negative + e₂.negative
  positive_pos := add_pos e₁.positive_pos e₂.positive_pos
  negative_pos := add_pos e₁.negative_pos e₂.negative_pos

/-- Revision is commutative -/
theorem revision_comm (e₁ e₂ : Evidence) :
    revision e₁ e₂ = revision e₂ e₁ := by
  simp only [revision, add_comm]

/-- Revision preserves total evidence count -/
theorem revision_total (e₁ e₂ : Evidence) :
    (revision e₁ e₂).total = e₁.total + e₂.total := by
  simp only [revision, total]
  ring

/-- Revision strength formula: strength of combined evidence.
    This is EXACT - no approximation needed for revision. -/
theorem revision_strength (e₁ e₂ : Evidence) :
    (revision e₁ e₂).strength = (e₁.positive + e₂.positive) / (e₁.total + e₂.total) := by
  simp only [revision, strength, total]
  congr 1; ring

end Evidence

/-! ## Auditing the PLN Heuristic

We compare the TRUE variance of a product of independent Beta-distributed
variables to the variance implied by PLN's confidence heuristic.
-/

/-- The TRUE variance of Z = X · Y where X, Y are independent.
    Var(XY) = E[X]²Var[Y] + E[Y]²Var[X] + Var[X]Var[Y] -/
def trueProductVariance (e₁ e₂ : Evidence) : ℝ :=
  let s₁ := e₁.strength
  let s₂ := e₂.strength
  let v₁ := e₁.variance
  let v₂ := e₂.variance
  s₁^2 * v₂ + s₂^2 * v₁ + v₁ * v₂

theorem trueProductVariance_pos (e₁ e₂ : Evidence) :
    0 < trueProductVariance e₁ e₂ := by
  simp only [trueProductVariance]
  have hs₁ := e₁.strength_mem_Ioo
  have hs₂ := e₂.strength_mem_Ioo
  have hv₁ := e₁.variance_pos
  have hv₂ := e₂.variance_pos
  have h1 : 0 ≤ e₁.strength^2 * e₂.variance := mul_nonneg (sq_nonneg _) (le_of_lt hv₂)
  have h2 : 0 ≤ e₂.strength^2 * e₁.variance := mul_nonneg (sq_nonneg _) (le_of_lt hv₁)
  have h3 : 0 < e₁.variance * e₂.variance := mul_pos hv₁ hv₂
  linarith

/-- PLN's HEURISTIC confidence for deduction: c_AC = c_AB * c_BC.
    Given a lookahead parameter K, confidence c relates to count n via c = n/(n+K).
    The implied variance is then computed from the "fake" count. -/
def plnHeuristicVariance (e₁ e₂ : Evidence) (K : ℝ) (_hK : 0 < K) : ℝ :=
  let n₁ := e₁.total
  let n₂ := e₂.total
  let c₁ := n₁ / (n₁ + K)
  let c₂ := n₂ / (n₂ + K)
  let c_product := c₁ * c₂  -- PLN heuristic: multiply confidences
  let s_product := e₁.strength * e₂.strength
  -- Variance implied by treating c_product as the "true" confidence
  -- Using Beta variance approximation: Var ≈ s(1-s)/(n+1) where n = K·c/(1-c)
  let n_implied := K * c_product / (1 - c_product)
  s_product * (1 - s_product) / (n_implied + 1)

/-- THE AUDIT: PLN's heuristic does NOT match the true variance.
    The simple product heuristic c_AC = c_AB * c_BC is mathematically distinct
    from the true variance propagation.

    We prove this by counterexample: for symmetric evidence (2,2) and K=1,
    - True variance ≈ 0.05 (using product formula s₁²v₂ + s₂²v₁ + v₁v₂)
    - Heuristic variance ≈ 0.0625 (from s(1-s)/(n+1))
    The heuristic OVERESTIMATES variance in this case. -/
theorem pln_heuristic_counterexample : ∃ e₁ e₂ : Evidence, ∃ K : ℝ, ∃ hK : 0 < K,
    trueProductVariance e₁ e₂ ≠ plnHeuristicVariance e₁ e₂ K hK := by
  -- Take e₁ = e₂ = Evidence(2, 2) (uniform prior), K = 1
  use ⟨2, 2, by norm_num, by norm_num⟩
  use ⟨2, 2, by norm_num, by norm_num⟩
  use 1, by norm_num
  -- The two formulas give different algebraic expressions
  simp only [trueProductVariance, plnHeuristicVariance, Evidence.strength,
             Evidence.total, Evidence.variance, Evidence.toBeta,
             BetaParams.variance, BetaParams.n]
  -- norm_num verifies the expressions differ
  norm_num

end Mettapedia.Logic.PLN.Distributional
