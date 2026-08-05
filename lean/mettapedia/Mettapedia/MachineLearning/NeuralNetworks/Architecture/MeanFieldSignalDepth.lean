import Mathlib

/-!
# Mean-field signal depth and the dropout critical-point boundary

Schoenholz, Gilmer, Ganguli, and Sohl-Dickstein, *Deep Information
Propagation* (ICLR 2017, arXiv:1611.01232), derive a local correlation
multiplier `χ` and the ordered-phase depth scale

`ξ⁻¹ = -log χ`.

They also show that independently sampled dropout masks move identical-input
correlation strictly below one whenever retention is below one and the
variance terms are nondegenerate.

This file makes the scalar depth-scale algebra exact at every finite depth. It
proves the exponential representation, a computable multiplier threshold for
any requested propagation horizon, constructive availability of arbitrarily
large finite depth scales below criticality, and the ordered/critical/chaotic
one-step boundaries. It then formalizes the exact algebra of the paper's
dropout correlation map at correlation one, including its monotonic retention
law and the degenerate boundary where dropout does not break the fixed point.

The Gaussian mean-field approximation, the source's activation integrals,
finite-width approximation error, gradient mean-field duality, and empirical
trainability claims are not formalized here. Runtime use therefore requires an
independent trace binding the measured correlation multiplier and variance
terms to these scalar quantities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace MeanFieldSignalDepth

noncomputable section

/-! ## Exact finite-depth linearized transport -/

/-- Exact solution of the linearized fixed-point residual recurrence. -/
def linearizedResidual (multiplier initial : ℝ) (depth : ℕ) : ℝ :=
  multiplier ^ depth * initial

@[simp] theorem linearizedResidual_zero (multiplier initial : ℝ) :
    linearizedResidual multiplier initial 0 = initial := by
  simp [linearizedResidual]

@[simp] theorem linearizedResidual_succ
    (multiplier initial : ℝ) (depth : ℕ) :
    linearizedResidual multiplier initial (depth + 1) =
      multiplier * linearizedResidual multiplier initial depth := by
  simp [linearizedResidual, pow_succ]
  ring

/-- The ordered-phase depth scale from Equation (9). -/
def correlationDepthScale (multiplier : ℝ) : ℝ :=
  1 / (-Real.log multiplier)

theorem correlationDepthScale_pos
    {multiplier : ℝ} (hpositive : 0 < multiplier)
    (hordered : multiplier < 1) :
    0 < correlationDepthScale multiplier := by
  exact one_div_pos.mpr (neg_pos.mpr (Real.log_neg hpositive hordered))

/-- The source's exponential depth-scale notation is exactly the finite power
of the linearized correlation multiplier. -/
theorem exp_neg_depth_div_correlationDepthScale
    {multiplier : ℝ} (hpositive : 0 < multiplier)
    (hordered : multiplier < 1) (depth : ℕ) :
    Real.exp (-(depth : ℝ) / correlationDepthScale multiplier) =
      multiplier ^ depth := by
  have hlog : Real.log multiplier ≠ 0 :=
    ne_of_lt (Real.log_neg hpositive hordered)
  have hexponent :
      -(depth : ℝ) / correlationDepthScale multiplier =
        (depth : ℝ) * Real.log multiplier := by
    simp [correlationDepthScale, div_eq_mul_inv]
  rw [hexponent, Real.exp_nat_mul, Real.exp_log hpositive]

theorem linearizedResidual_eq_depthScale_exp
    {multiplier : ℝ} (hpositive : 0 < multiplier)
    (hordered : multiplier < 1) (initial : ℝ) (depth : ℕ) :
    linearizedResidual multiplier initial depth =
      Real.exp (-(depth : ℝ) / correlationDepthScale multiplier) *
        initial := by
  rw [exp_neg_depth_div_correlationDepthScale hpositive hordered]
  rfl

/-- A requested propagation horizon is below the correlation depth scale
exactly when the multiplier exceeds an explicit exponential threshold. -/
theorem budget_lt_correlationDepthScale_iff
    {multiplier budget : ℝ} (hpositive : 0 < multiplier)
    (hordered : multiplier < 1) (hbudget : 0 < budget) :
    budget < correlationDepthScale multiplier ↔
      Real.exp (-1 / budget) < multiplier := by
  have hlogneg : Real.log multiplier < 0 :=
    Real.log_neg hpositive hordered
  have hdenominator : 0 < -Real.log multiplier :=
    neg_pos.mpr hlogneg
  constructor
  · intro hscale
    apply (Real.lt_log_iff_exp_lt hpositive).mp
    have hproduct :
        budget * (-Real.log multiplier) < 1 := by
      exact (lt_div_iff₀ hdenominator).mp
        (by simpa [correlationDepthScale] using hscale)
    exact (div_lt_iff₀ hbudget).2 (by nlinarith)
  · intro hthreshold
    have hlogBound : -1 / budget < Real.log multiplier :=
      (Real.lt_log_iff_exp_lt hpositive).mpr hthreshold
    have hproduct :
        budget * (-Real.log multiplier) < 1 := by
      have hcross := (div_lt_iff₀ hbudget).mp hlogBound
      nlinarith
    have hscale := (lt_div_iff₀ hdenominator).2 hproduct
    simpa [correlationDepthScale] using hscale

/-- Every finite requested horizon can be attained by a strictly
subcritical multiplier. This is a constructive finite-depth version of the
source's divergence statement at the edge of chaos. -/
theorem exists_subcritical_multiplier_with_depthScale_gt
    {budget : ℝ} (hbudget : 0 < budget) :
    ∃ multiplier : ℝ,
      0 < multiplier ∧ multiplier < 1 ∧
        budget < correlationDepthScale multiplier := by
  let multiplier := Real.exp (-1 / (2 * budget))
  have hpositive : 0 < multiplier := Real.exp_pos _
  have htwice : 0 < 2 * budget := mul_pos (by norm_num) hbudget
  have hexponent : -1 / (2 * budget) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) htwice
  have hordered : multiplier < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hexponent
  refine ⟨multiplier, hpositive, hordered,
    (budget_lt_correlationDepthScale_iff
      hpositive hordered hbudget).2 ?_⟩
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff₀ hbudget htwice).2
  nlinarith

/-- In the ordered phase, every nonzero linearized residual shrinks strictly
at each layer. -/
theorem ordered_linearizedResidual_strictly_contracts
    {multiplier initial : ℝ} (hpositive : 0 < multiplier)
    (hordered : multiplier < 1) (hinitial : initial ≠ 0)
    (depth : ℕ) :
    |linearizedResidual multiplier initial (depth + 1)| <
      |linearizedResidual multiplier initial depth| := by
  rw [linearizedResidual_succ, abs_mul, abs_of_pos hpositive]
  have hresidual :
      0 < |linearizedResidual multiplier initial depth| := by
    apply abs_pos.mpr
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hpositive)) hinitial
  nlinarith

/-- At criticality the linearized residual does not decay at any depth. -/
@[simp] theorem critical_linearizedResidual
    (initial : ℝ) (depth : ℕ) :
    linearizedResidual 1 initial depth = initial := by
  simp [linearizedResidual]

/-- In the chaotic phase, every nonzero linearized residual grows strictly at
each layer. -/
theorem chaotic_linearizedResidual_strictly_expands
    {multiplier initial : ℝ} (hchaotic : 1 < multiplier)
    (hinitial : initial ≠ 0) (depth : ℕ) :
    |linearizedResidual multiplier initial depth| <
      |linearizedResidual multiplier initial (depth + 1)| := by
  have hpositive : 0 < multiplier := lt_trans zero_lt_one hchaotic
  rw [linearizedResidual_succ, abs_mul, abs_of_pos hpositive]
  have hresidual :
      0 < |linearizedResidual multiplier initial depth| := by
    apply abs_pos.mpr
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hpositive)) hinitial
  nlinarith

/-! ## Independent-mask dropout at identical-input correlation -/

/-- Equation (13), with the activation integral represented by its
nonnegative second-moment scalar. `retention = 1` means no dropout. -/
def dropoutCorrelationAtOne
    (retention fixedVariance weightVariance activationSecondMoment : ℝ) : ℝ :=
  1 -
    ((1 - retention) / (retention * fixedVariance)) *
      weightVariance * activationSecondMoment

@[simp] theorem dropoutCorrelationAtOne_no_dropout
    (fixedVariance weightVariance activationSecondMoment : ℝ) :
    dropoutCorrelationAtOne 1 fixedVariance weightVariance
      activationSecondMoment = 1 := by
  simp [dropoutCorrelationAtOne]

/-- Any nontrivial independently sampled dropout moves correlation one
strictly below one when all variance terms are nondegenerate. -/
theorem dropoutCorrelationAtOne_lt_one
    {retention fixedVariance weightVariance activationSecondMoment : ℝ}
    (hretentionPositive : 0 < retention)
    (hretentionDropout : retention < 1)
    (hfixedVariance : 0 < fixedVariance)
    (hweightVariance : 0 < weightVariance)
    (hactivationSecondMoment : 0 < activationSecondMoment) :
    dropoutCorrelationAtOne retention fixedVariance weightVariance
      activationSecondMoment < 1 := by
  unfold dropoutCorrelationAtOne
  have hdenominator : 0 < retention * fixedVariance :=
    mul_pos hretentionPositive hfixedVariance
  have hratio :
      0 < (1 - retention) / (retention * fixedVariance) :=
    div_pos (sub_pos.mpr hretentionDropout) hdenominator
  have hproduct :
      0 <
        ((1 - retention) / (retention * fixedVariance)) *
          weightVariance * activationSecondMoment :=
    mul_pos (mul_pos hratio hweightVariance) hactivationSecondMoment
  linarith

/-- Higher retention preserves strictly more identical-input correlation when
the variance terms are positive. -/
theorem dropoutCorrelationAtOne_strictMono_retention
    {first second fixedVariance weightVariance activationSecondMoment : ℝ}
    (hfirstPositive : 0 < first) (hfirstSecond : first < second)
    (hfixedVariance : 0 < fixedVariance)
    (hweightVariance : 0 < weightVariance)
    (hactivationSecondMoment : 0 < activationSecondMoment) :
    dropoutCorrelationAtOne first fixedVariance weightVariance
        activationSecondMoment <
      dropoutCorrelationAtOne second fixedVariance weightVariance
        activationSecondMoment := by
  unfold dropoutCorrelationAtOne
  have hsecondPositive : 0 < second :=
    lt_trans hfirstPositive hfirstSecond
  have hfraction :
      (1 - second) / (second * fixedVariance) <
        (1 - first) / (first * fixedVariance) := by
    rw [div_lt_div_iff₀
      (mul_pos hsecondPositive hfixedVariance)
      (mul_pos hfirstPositive hfixedVariance)]
    nlinarith
  have hmomentProduct :
      0 < weightVariance * activationSecondMoment :=
    mul_pos hweightVariance hactivationSecondMoment
  nlinarith

/-- Positivity of the activation second moment is load-bearing: if the
activation is identically zero, dropout leaves correlation one fixed. -/
@[simp] theorem dropoutCorrelationAtOne_zero_activationMoment
    (retention fixedVariance weightVariance : ℝ) :
    dropoutCorrelationAtOne retention fixedVariance weightVariance 0 = 1 := by
  simp [dropoutCorrelationAtOne]

theorem ordered_half :
    linearizedResidual (1 / 2) 8 3 = 1 ∧
      0 < correlationDepthScale (1 / 2) := by
  constructor
  · norm_num [linearizedResidual]
  · exact correlationDepthScale_pos (by norm_num) (by norm_num)

theorem dropout_example :
    dropoutCorrelationAtOne (1 / 2) 2 3 4 = -5 ∧
      dropoutCorrelationAtOne 1 2 3 4 = 1 ∧
      dropoutCorrelationAtOne (1 / 2) 2 3 0 = 1 := by
  norm_num [dropoutCorrelationAtOne]

#print axioms exp_neg_depth_div_correlationDepthScale
#print axioms budget_lt_correlationDepthScale_iff
#print axioms exists_subcritical_multiplier_with_depthScale_gt
#print axioms ordered_linearizedResidual_strictly_contracts
#print axioms critical_linearizedResidual
#print axioms chaotic_linearizedResidual_strictly_expands
#print axioms dropoutCorrelationAtOne_lt_one
#print axioms dropoutCorrelationAtOne_strictMono_retention
#print axioms dropoutCorrelationAtOne_zero_activationMoment
#print axioms ordered_half
#print axioms dropout_example

end

end MeanFieldSignalDepth

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
