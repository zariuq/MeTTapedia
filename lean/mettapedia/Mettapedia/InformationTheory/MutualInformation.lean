import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mettapedia.InformationTheory.Basic

/-!
# Mutual Information and Log-Ratio Information Gain

This file separates two closely related but distinct objects:

1. **Pointwise / log-ratio information gain** for a single posterior/prior update
2. **Shannon mutual information** for a finite joint distribution

The former is the scalar that fits identities of the form
`posterior = prior * 2^score`.
The latter is an expectation of log-ratio terms across a whole joint distribution.
-/

namespace Mettapedia.InformationTheory

open Real Finset BigOperators
open scoped BigOperators
/-- Base-2 logarithm, packaged on top of `Real.log`. -/
noncomputable def logBase2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Pointwise log-ratio information gain, measured in bits.

Given a posterior and prior probability, this is the base-2 log of the update ratio.
It is the right scalar for identities of the form `posterior = prior * 2^score`. -/
noncomputable def logRatioInformationGainBits (posterior prior : ℝ) : ℝ :=
  if 0 < posterior ∧ 0 < prior then
    logBase2 (posterior / prior)
  else
    0

theorem logRatioInformationGainBits_eq_logBase2_ratio
    {posterior prior : ℝ}
    (hPosterior : 0 < posterior) (hPrior : 0 < prior) :
    logRatioInformationGainBits posterior prior = logBase2 (posterior / prior) := by
  unfold logRatioInformationGainBits
  rw [if_pos ⟨hPosterior, hPrior⟩]

theorem logRatioInformationGainBits_eq_log2_ratio
    {posterior prior : ℝ}
    (hPosterior : 0 < posterior) (hPrior : 0 < prior) :
    logRatioInformationGainBits posterior prior =
      Real.log (posterior / prior) / Real.log 2 := by
  rw [logRatioInformationGainBits_eq_logBase2_ratio hPosterior hPrior]
  rfl

theorem two_rpow_logBase2 {x : ℝ} (hx : 0 < x) :
    (2 : ℝ).rpow (logBase2 x) = x := by
  have hTwo : 0 < (2 : ℝ) := by norm_num
  have hLogTwoNe : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hdef :
      (2 : ℝ).rpow (Real.log x / Real.log 2) =
        Real.exp (Real.log 2 * (Real.log x / Real.log 2)) := by
    simpa using (Real.rpow_def_of_pos hTwo (Real.log x / Real.log 2))
  unfold logBase2
  rw [hdef]
  have hMul :
      Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by
    field_simp [hLogTwoNe]
  rw [hMul, Real.exp_log hx]

theorem posterior_eq_prior_mul_two_rpow_logRatioInformationGainBits
    {posterior prior : ℝ}
    (hPosterior : 0 < posterior) (hPrior : 0 < prior) :
    posterior = prior * (2 : ℝ).rpow (logRatioInformationGainBits posterior prior) := by
  rw [logRatioInformationGainBits_eq_logBase2_ratio hPosterior hPrior]
  rw [two_rpow_logBase2 (div_pos hPosterior hPrior)]
  have hPriorNe : prior ≠ 0 := ne_of_gt hPrior
  rw [div_eq_mul_inv]
  calc
    posterior = posterior * 1 := by ring
    _ = posterior * (prior * prior⁻¹) := by rw [mul_inv_cancel₀ hPriorNe, mul_one]
    _ = prior * (posterior * prior⁻¹) := by ring

/-- A finite joint probability distribution on `Fin m × Fin n`. -/
abbrev JointProb (m n : ℕ) := Prob (Fin m × Fin n)

namespace JointProb

variable {m n : ℕ}

/-- Left marginal of a finite joint distribution. -/
noncomputable def marginalLeft (joint : JointProb m n) : Prob (Fin m) :=
  ⟨fun a => ∑ b, joint.1 (a, b), by
    constructor
    · intro a
      exact Finset.sum_nonneg (fun b _ => joint.2.1 (a, b))
    ·
      classical
      simpa [Fintype.sum_prod_type] using joint.2.2⟩

/-- Right marginal of a finite joint distribution. -/
noncomputable def marginalRight (joint : JointProb m n) : Prob (Fin n) :=
  ⟨fun b => ∑ a, joint.1 (a, b), by
    constructor
    · intro b
      exact Finset.sum_nonneg (fun a _ => joint.2.1 (a, b))
    ·
      classical
      calc
        (∑ b : Fin n, ∑ a : Fin m, joint.1 (a, b))
            = ∑ ba : Fin n × Fin m, joint.1 (ba.2, ba.1) := by
                simp [Fintype.sum_prod_type]
        _ = ∑ ab : Fin m × Fin n, joint.1 ab := by
              exact (Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin m))
                  (fun ab : Fin m × Fin n => joint.1 ab))
        _ = 1 := joint.2.2⟩

/-- Independent coupling of two marginals. -/
noncomputable def independentCoupling (left : Prob (Fin m)) (right : Prob (Fin n)) :
    JointProb m n :=
  ⟨fun ab => left.1 ab.1 * right.1 ab.2, by
    constructor
    · intro ab
      exact mul_nonneg (left.2.1 ab.1) (right.2.1 ab.2)
    ·
      classical
      rw [Fintype.sum_prod_type]
      calc
        (∑ a : Fin m, ∑ b : Fin n, left.1 a * right.1 b)
            = ∑ a : Fin m, left.1 a * (∑ b : Fin n, right.1 b) := by
                congr 1
                ext a
                rw [Finset.mul_sum]
        _ = ∑ a : Fin m, left.1 a * 1 := by rw [right.2.2]
        _ = ∑ a : Fin m, left.1 a := by simp
        _ = 1 := left.2.2⟩

/-- The product of the left and right marginals of a joint distribution. -/
noncomputable def productOfMarginals (joint : JointProb m n) : JointProb m n :=
  independentCoupling (marginalLeft joint) (marginalRight joint)

/-- Shannon mutual information, measured in nats, defined as KL divergence from the
joint distribution to the product of its marginals. In the finite case, this is the
expected log-ratio under the joint law. -/
noncomputable def shannonMutualInformationNats (joint : JointProb m n) : ℝ :=
  ∑ ab : Fin m × Fin n,
    joint.1 ab * Real.log (joint.1 ab / (productOfMarginals joint).1 ab)

/-- The expected log-ratio form of mutual information, measured in nats. -/
noncomputable def expectedLogRatioToProductNats (joint : JointProb m n) : ℝ :=
  ∑ ab : Fin m × Fin n,
    joint.1 ab * Real.log (joint.1 ab / (productOfMarginals joint).1 ab)

theorem shannonMutualInformationNats_eq_expectedLogRatioToProductNats
    (joint : JointProb m n) :
    shannonMutualInformationNats joint = expectedLogRatioToProductNats joint := by
  rfl

/-- Shannon mutual information, measured in bits. -/
noncomputable def shannonMutualInformationBits (joint : JointProb m n) : ℝ :=
  shannonMutualInformationNats joint / Real.log 2

/-- Expected log-ratio information gain, measured in bits. -/
noncomputable def expectedLogRatioToProductBits (joint : JointProb m n) : ℝ :=
  expectedLogRatioToProductNats joint / Real.log 2

theorem shannonMutualInformationBits_eq_expectedLogRatioToProductBits
    (joint : JointProb m n) :
    shannonMutualInformationBits joint = expectedLogRatioToProductBits joint := by
  unfold shannonMutualInformationBits expectedLogRatioToProductBits
  rw [shannonMutualInformationNats_eq_expectedLogRatioToProductNats]

end JointProb

end Mettapedia.InformationTheory
