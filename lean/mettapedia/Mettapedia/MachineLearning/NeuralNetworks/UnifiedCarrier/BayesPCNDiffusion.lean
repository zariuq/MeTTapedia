import Mathlib

/-!
# BayesPCN diffusion forgetting

Yoo, Wood, et al., *BayesPCN: A Continually Learnable Predictive Coding
Associative Memory* (arXiv:2205.09930), Section 4.3 and Appendix D,
Equations (29)--(32), diffuse a Gaussian parameter posterior toward its empty
memory prior.  If `retention = 1 - beta`, the mean coefficient is
`sqrt retention`, while the covariance coefficient is `retention`.

This file generalizes those two affine formulae to arbitrary real normed
spaces and proves their reusable algebra:

* the displayed affine formulae are recovered exactly;
* successive forget operations form a semigroup, with
  `beta₁ ⊕ beta₂ = beta₁ + beta₂ - beta₁ * beta₂`;
* finite iteration has an exact geometric closed form;
* strict forgetting converges to the declared prior;
* zero and unit forgetting recover the current state and prior respectively.

The source restricts `beta` to `[0, 1]`.  An executable counterexample below
shows why extending the covariance formula beyond that domain is not a
convex diffusion.  Nothing here asserts correctness of BayesPCN's approximate
particle posterior, nonlinear recall, or trained-network implementation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Set

section Diffusion

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Diffuse a posterior mean toward its prior with coefficient
`sqrt retention`, as in BayesPCN Equations (29) and (31). -/
noncomputable def meanDiffuse
    (retention : ℝ) (prior current : State) : State :=
  prior + Real.sqrt retention • (current - prior)

/-- Diffuse a posterior covariance toward its prior with coefficient
`retention`, as in BayesPCN Equations (30) and (32). -/
noncomputable def covarianceDiffuse
    (retention : ℝ) (prior current : State) : State :=
  prior + retention • (current - prior)

/-- BayesPCN's retention coordinate corresponding to forget strength `beta`. -/
def forgetRetention (beta : ℝ) : ℝ :=
  1 - beta

/-- Effective forget strength of two successive diffusion steps. -/
def composeForget (first second : ℝ) : ℝ :=
  first + second - first * second

/-- BayesPCN mean diffusion, parameterized by forget strength. -/
noncomputable def bayesPCNMeanForget
    (beta : ℝ) (prior current : State) : State :=
  meanDiffuse (forgetRetention beta) prior current

/-- BayesPCN covariance diffusion, parameterized by forget strength. -/
noncomputable def bayesPCNCovarianceForget
    (beta : ℝ) (prior current : State) : State :=
  covarianceDiffuse (forgetRetention beta) prior current

/-- The prior-centered mean form is exactly the source's weighted formula. -/
theorem meanDiffuse_eq_source_formula
    (retention : ℝ) (prior current : State) :
    meanDiffuse retention prior current =
      Real.sqrt retention • current +
        (1 - Real.sqrt retention) • prior := by
  unfold meanDiffuse
  module

/-- The prior-centered covariance form is exactly the source's weighted
formula. -/
theorem covarianceDiffuse_eq_source_formula
    (retention : ℝ) (prior current : State) :
    covarianceDiffuse retention prior current =
      retention • current + (1 - retention) • prior := by
  unfold covarianceDiffuse
  module

@[simp] theorem meanDiffuse_one (prior current : State) :
    meanDiffuse 1 prior current = current := by
  simp [meanDiffuse]

@[simp] theorem meanDiffuse_zero (prior current : State) :
    meanDiffuse 0 prior current = prior := by
  simp [meanDiffuse]

@[simp] theorem covarianceDiffuse_one (prior current : State) :
    covarianceDiffuse 1 prior current = current := by
  simp [covarianceDiffuse]

@[simp] theorem covarianceDiffuse_zero (prior current : State) :
    covarianceDiffuse 0 prior current = prior := by
  simp [covarianceDiffuse]

/-- Mean diffusion composes by multiplying retentions. -/
theorem meanDiffuse_compose
    (first second : ℝ) (prior current : State) (hfirst : 0 ≤ first) :
    meanDiffuse first prior (meanDiffuse second prior current) =
      meanDiffuse (first * second) prior current := by
  rw [meanDiffuse_eq_source_formula, meanDiffuse_eq_source_formula,
    meanDiffuse_eq_source_formula, Real.sqrt_mul hfirst]
  module

/-- Covariance diffusion composes by multiplying retentions. -/
theorem covarianceDiffuse_compose
    (first second : ℝ) (prior current : State) :
    covarianceDiffuse first prior
        (covarianceDiffuse second prior current) =
      covarianceDiffuse (first * second) prior current := by
  simp only [covarianceDiffuse]
  module

/-- The effective forget operation is exactly multiplication in retention
coordinates. -/
theorem forgetRetention_compose (first second : ℝ) :
    forgetRetention (composeForget first second) =
      forgetRetention first * forgetRetention second := by
  unfold forgetRetention composeForget
  ring

/-- Valid forget strengths have valid retention. -/
theorem forgetRetention_mem_Icc
    {beta : ℝ} (hbeta : beta ∈ Icc (0 : ℝ) 1) :
    forgetRetention beta ∈ Icc (0 : ℝ) 1 := by
  constructor <;> unfold forgetRetention <;> linarith [hbeta.1, hbeta.2]

/-- The effective strength of two valid forget operations remains valid. -/
theorem composeForget_mem_Icc
    {first second : ℝ}
    (hfirst : first ∈ Icc (0 : ℝ) 1)
    (hsecond : second ∈ Icc (0 : ℝ) 1) :
    composeForget first second ∈ Icc (0 : ℝ) 1 := by
  have hleft :
      0 ≤ first * (1 - second) :=
    mul_nonneg hfirst.1 (sub_nonneg.mpr hsecond.2)
  have hright :
      0 ≤ (1 - first) * (1 - second) :=
    mul_nonneg (sub_nonneg.mpr hfirst.2) (sub_nonneg.mpr hsecond.2)
  constructor
  · calc
      0 ≤ first * (1 - second) + second :=
        add_nonneg hleft hsecond.1
      _ = composeForget first second := by
        unfold composeForget
        ring
  · have hcomplement :
        0 ≤ 1 - composeForget first second := by
      calc
        0 ≤ (1 - first) * (1 - second) := hright
        _ = 1 - composeForget first second := by
          unfold composeForget
          ring
    exact sub_nonneg.mp hcomplement

/-- Successive valid mean-forget steps equal one step at the composed
strength. -/
theorem bayesPCNMeanForget_compose
    (first second : ℝ) (prior current : State) (hfirst : first ≤ 1) :
    bayesPCNMeanForget first prior
        (bayesPCNMeanForget second prior current) =
      bayesPCNMeanForget (composeForget first second) prior current := by
  unfold bayesPCNMeanForget
  calc
    meanDiffuse (forgetRetention first) prior
        (meanDiffuse (forgetRetention second) prior current) =
      meanDiffuse
        (forgetRetention first * forgetRetention second) prior current :=
      meanDiffuse_compose _ _ _ _ (by
        unfold forgetRetention
        linarith)
    _ = meanDiffuse (forgetRetention (composeForget first second))
        prior current := by
      rw [forgetRetention_compose]

/-- Successive covariance-forget steps equal one step at the composed
strength. -/
theorem bayesPCNCovarianceForget_compose
    (first second : ℝ) (prior current : State) :
    bayesPCNCovarianceForget first prior
        (bayesPCNCovarianceForget second prior current) =
      bayesPCNCovarianceForget (composeForget first second)
        prior current := by
  unfold bayesPCNCovarianceForget
  calc
    covarianceDiffuse (forgetRetention first) prior
        (covarianceDiffuse (forgetRetention second) prior current) =
      covarianceDiffuse
        (forgetRetention first * forgetRetention second) prior current :=
      covarianceDiffuse_compose _ _ _ _
    _ = covarianceDiffuse (forgetRetention (composeForget first second))
        prior current := by
      rw [forgetRetention_compose]

@[simp] theorem bayesPCNMeanForget_zero (prior current : State) :
    bayesPCNMeanForget 0 prior current = current := by
  simp [bayesPCNMeanForget, forgetRetention]

@[simp] theorem bayesPCNMeanForget_one (prior current : State) :
    bayesPCNMeanForget 1 prior current = prior := by
  simp [bayesPCNMeanForget, forgetRetention]

@[simp] theorem bayesPCNCovarianceForget_zero (prior current : State) :
    bayesPCNCovarianceForget 0 prior current = current := by
  simp [bayesPCNCovarianceForget, forgetRetention]

@[simp] theorem bayesPCNCovarianceForget_one (prior current : State) :
    bayesPCNCovarianceForget 1 prior current = prior := by
  simp [bayesPCNCovarianceForget, forgetRetention]

/-- Exact finite-time mean trajectory under repeated fixed retention. -/
theorem meanDiffuse_iterate
    (retention : ℝ) (prior current : State) (steps : ℕ) :
    (meanDiffuse retention prior)^[steps] current =
      prior + (Real.sqrt retention) ^ steps • (current - prior) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [meanDiffuse, pow_succ]
      module

/-- Exact finite-time covariance trajectory under repeated fixed retention. -/
theorem covarianceDiffuse_iterate
    (retention : ℝ) (prior current : State) (steps : ℕ) :
    (covarianceDiffuse retention prior)^[steps] current =
      prior + retention ^ steps • (current - prior) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [covarianceDiffuse, pow_succ]
      module

/-- Repeated strict mean diffusion converges to the prior.  The theorem is
slightly stronger than the source domain: Lean's real square root maps a
negative retention to zero, so only `retention < 1` is algebraically needed. -/
theorem meanDiffuse_iterate_tendsto_prior
    (retention : ℝ) (prior current : State) (hretention : retention < 1) :
    Filter.Tendsto
      (fun steps => (meanDiffuse retention prior)^[steps] current)
      Filter.atTop (nhds prior) := by
  rw [show
      (fun steps => (meanDiffuse retention prior)^[steps] current) =
        (fun steps =>
          prior + (Real.sqrt retention) ^ steps • (current - prior)) by
      funext steps
      exact meanDiffuse_iterate retention prior current steps]
  have hsqrtNonneg : 0 ≤ Real.sqrt retention :=
    Real.sqrt_nonneg retention
  have hsqrtLtOne : Real.sqrt retention < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    simpa using hretention
  have hpow :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hsqrtNonneg hsqrtLtOne
  simpa using
    tendsto_const_nhds.add (hpow.smul_const (current - prior))

/-- Repeated strict covariance diffusion converges to the prior. -/
theorem covarianceDiffuse_iterate_tendsto_prior
    (retention : ℝ) (prior current : State)
    (hretentionNonneg : 0 ≤ retention) (hretentionLtOne : retention < 1) :
    Filter.Tendsto
      (fun steps => (covarianceDiffuse retention prior)^[steps] current)
      Filter.atTop (nhds prior) := by
  rw [show
      (fun steps => (covarianceDiffuse retention prior)^[steps] current) =
        (fun steps => prior + retention ^ steps • (current - prior)) by
      funext steps
      exact covarianceDiffuse_iterate retention prior current steps]
  have hpow :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hretentionNonneg hretentionLtOne
  simpa using
    tendsto_const_nhds.add (hpow.smul_const (current - prior))

end Diffusion

/-! ## Joint Gaussian state and executable boundaries -/

/-- The two posterior summaries changed by BayesPCN's diffusion operation. -/
structure GaussianMomentState (Mean Covariance : Type*) where
  mean : Mean
  covariance : Covariance

@[ext] theorem GaussianMomentState.extensionality
    {Mean Covariance : Type*}
    {left right : GaussianMomentState Mean Covariance}
    (hmean : left.mean = right.mean)
    (hcovariance : left.covariance = right.covariance) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Diffuse both Gaussian moments with their source-specific coefficients. -/
noncomputable def bayesPCNForget
    {Mean Covariance : Type*}
    [NormedAddCommGroup Mean] [NormedSpace ℝ Mean]
    [NormedAddCommGroup Covariance] [NormedSpace ℝ Covariance]
    (beta : ℝ)
    (prior current : GaussianMomentState Mean Covariance) :
    GaussianMomentState Mean Covariance where
  mean := bayesPCNMeanForget beta prior.mean current.mean
  covariance :=
    bayesPCNCovarianceForget beta prior.covariance current.covariance

theorem bayesPCNForget_compose
    {Mean Covariance : Type*}
    [NormedAddCommGroup Mean] [NormedSpace ℝ Mean]
    [NormedAddCommGroup Covariance] [NormedSpace ℝ Covariance]
    (first second : ℝ)
    (prior current : GaussianMomentState Mean Covariance)
    (hfirst : first ≤ 1) :
    bayesPCNForget first prior (bayesPCNForget second prior current) =
      bayesPCNForget (composeForget first second) prior current := by
  ext
  · exact bayesPCNMeanForget_compose
      first second prior.mean current.mean hfirst
  · exact bayesPCNCovarianceForget_compose
      first second prior.covariance current.covariance

@[simp] theorem bayesPCNForget_zero
    {Mean Covariance : Type*}
    [NormedAddCommGroup Mean] [NormedSpace ℝ Mean]
    [NormedAddCommGroup Covariance] [NormedSpace ℝ Covariance]
    (prior current : GaussianMomentState Mean Covariance) :
    bayesPCNForget 0 prior current = current := by
  ext <;> simp [bayesPCNForget]

@[simp] theorem bayesPCNForget_one
    {Mean Covariance : Type*}
    [NormedAddCommGroup Mean] [NormedSpace ℝ Mean]
    [NormedAddCommGroup Covariance] [NormedSpace ℝ Covariance]
    (prior current : GaussianMomentState Mean Covariance) :
    bayesPCNForget 1 prior current = prior := by
  ext <;> simp [bayesPCNForget]

noncomputable def scalarEmptyMemory : GaussianMomentState ℝ ℝ :=
  ⟨0, 0⟩

noncomputable def scalarUnitPosterior : GaussianMomentState ℝ ℝ :=
  ⟨1, 1⟩

/-- Positive fixture: forget strength `3/4` retains one half of the mean
displacement and one quarter of the covariance displacement. -/
theorem threeQuarterForget :
    bayesPCNForget (3 / 4) scalarEmptyMemory scalarUnitPosterior =
      (⟨1 / 2, 1 / 4⟩ : GaussianMomentState ℝ ℝ) := by
  ext <;>
    norm_num [bayesPCNForget, bayesPCNMeanForget,
      bayesPCNCovarianceForget, meanDiffuse, covarianceDiffuse,
      forgetRetention, scalarEmptyMemory, scalarUnitPosterior]

/-- Negative boundary: outside `beta ∈ [0,1]`, the covariance update is no
longer a convex interpolation and can cross beyond the prior. -/
theorem outOfRangeForget_is_not_diffusion :
    bayesPCNForget 2 scalarEmptyMemory scalarUnitPosterior =
      (⟨0, -1⟩ : GaussianMomentState ℝ ℝ) := by
  ext <;>
    norm_num [bayesPCNForget, bayesPCNMeanForget,
      bayesPCNCovarianceForget, meanDiffuse, covarianceDiffuse,
      forgetRetention, scalarEmptyMemory, scalarUnitPosterior]

#print axioms meanDiffuse_eq_source_formula
#print axioms covarianceDiffuse_eq_source_formula
#print axioms meanDiffuse_compose
#print axioms covarianceDiffuse_compose
#print axioms composeForget_mem_Icc
#print axioms bayesPCNForget_compose
#print axioms meanDiffuse_iterate
#print axioms covarianceDiffuse_iterate
#print axioms meanDiffuse_iterate_tendsto_prior
#print axioms covarianceDiffuse_iterate_tendsto_prior
#print axioms threeQuarterForget
#print axioms outOfRangeForget_is_not_diffusion

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
