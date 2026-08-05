import Mathlib

/-!
# Meta-transfer signals for causal structure

Bengio et al. (2019) propose selecting a causal factorization by how quickly it
adapts after a sparse distributional change.  Two exact algebraic claims are
isolated here.

First, a correctly learned finite categorical module whose conditional law did
not change has zero expected score in every tangent direction of the
probability simplex.  Evaluating the same score under a shifted distribution
need not vanish.

Second, for two structural hypotheses with positive online likelihoods
`L₁,L₂`, the source mixture

`sigmoid γ * L₁ + (1 - sigmoid γ) * L₂`

has negative-log derivative equal to the current prior probability minus the
posterior probability of the first hypothesis.  The sign is therefore exactly
the sign of `L₂ - L₁`: gradient descent moves toward the hypothesis with
larger online likelihood.  Equal likelihoods provide no structural signal, and
zero likelihoods violate the positivity premise.

These results recover Proposition 1 in the finite categorical setting and
Proposition 2 of *A Meta-Transfer Objective for Learning to Disentangle Causal
Mechanisms*.  They do not establish sparse mechanism shifts, identify a causal
graph from observational data, or prove the stochastic convergence and sample
complexity claims in the source.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace MetaTransferCausalStructure

noncomputable section

open scoped BigOperators

/-! ## Unchanged finite categorical mechanisms -/

/-- Expected score of a model-probability tangent under an evaluation law. -/
def expectedScore {Outcome : Type*} [Fintype Outcome]
    (evaluation probability tangent : Outcome → ℝ) : ℝ :=
  ∑ outcome, evaluation outcome *
    (tangent outcome / probability outcome)

/-- At a correctly matched positive categorical law, every tangent direction
of the probability simplex has zero expected score. -/
theorem expectedScore_eq_zero_of_matched
    {Outcome : Type*} [Fintype Outcome]
    (probability tangent : Outcome → ℝ)
    (hpositive : ∀ outcome, 0 < probability outcome)
    (htangent : ∑ outcome, tangent outcome = 0) :
    expectedScore probability probability tangent = 0 := by
  rw [show expectedScore probability probability tangent =
      ∑ outcome, tangent outcome by
    unfold expectedScore
    apply Finset.sum_congr rfl
    intro outcome _
    field_simp [(hpositive outcome).ne']]
  exact htangent

/-- A distribution shift can make the same normalized model tangent carry a
nonzero expected score. -/
theorem shifted_distribution_nonzero_expectedScore :
    expectedScore
      (fun outcome : Fin 2 => if outcome = 0 then (3 / 4 : ℝ) else 1 / 4)
      (fun _ : Fin 2 => (1 / 2 : ℝ))
      (fun outcome : Fin 2 => if outcome = 0 then (1 / 4 : ℝ) else -(1 / 4)) =
      1 / 4 := by
  norm_num [expectedScore, Fin.sum_univ_two]

/-- Positive fixture for the unchanged-mechanism endpoint. -/
theorem matched_distribution_zero_expectedScore :
    expectedScore
      (fun _ : Fin 2 => (1 / 2 : ℝ))
      (fun _ : Fin 2 => (1 / 2 : ℝ))
      (fun outcome : Fin 2 => if outcome = 0 then (1 / 4 : ℝ) else -(1 / 4)) =
      0 := by
  norm_num [expectedScore, Fin.sum_univ_two]

/-! ## Two-hypothesis meta-transfer regret -/

/-- Online likelihood of a two-hypothesis structural mixture. -/
def mixtureLikelihood
    (structuralLogit firstLikelihood secondLikelihood : ℝ) : ℝ :=
  Real.sigmoid structuralLogit * firstLikelihood +
    (1 - Real.sigmoid structuralLogit) * secondLikelihood

/-- Posterior weight of the first structural hypothesis after one transfer
episode, using its online likelihood as evidence. -/
def firstHypothesisPosterior
    (structuralLogit firstLikelihood secondLikelihood : ℝ) : ℝ :=
  Real.sigmoid structuralLogit * firstLikelihood /
    mixtureLikelihood structuralLogit firstLikelihood secondLikelihood

/-- Negative log-likelihood accumulated by the two-hypothesis mixture. -/
def metaTransferRegret
    (structuralLogit firstLikelihood secondLikelihood : ℝ) : ℝ :=
  -Real.log
    (mixtureLikelihood structuralLogit firstLikelihood secondLikelihood)

/-- Structural derivative appearing in the source's Proposition 2. -/
def metaTransferGradient
    (structuralLogit firstLikelihood secondLikelihood : ℝ) : ℝ :=
  Real.sigmoid structuralLogit -
    firstHypothesisPosterior
      structuralLogit firstLikelihood secondLikelihood

theorem mixtureLikelihood_pos
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    0 < mixtureLikelihood
      structuralLogit firstLikelihood secondLikelihood := by
  unfold mixtureLikelihood
  exact add_pos
    (mul_pos (Real.sigmoid_pos structuralLogit) hfirst)
    (mul_pos
      (sub_pos.mpr (Real.sigmoid_lt_one structuralLogit)) hsecond)

theorem firstHypothesisPosterior_pos
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    0 < firstHypothesisPosterior
      structuralLogit firstLikelihood secondLikelihood := by
  exact div_pos
    (mul_pos (Real.sigmoid_pos structuralLogit) hfirst)
    (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)

theorem firstHypothesisPosterior_lt_one
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    firstHypothesisPosterior
        structuralLogit firstLikelihood secondLikelihood < 1 := by
  rw [firstHypothesisPosterior, div_lt_one
    (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)]
  unfold mixtureLikelihood
  linarith [mul_pos
    (sub_pos.mpr (Real.sigmoid_lt_one structuralLogit)) hsecond]

/-- Exact source equation:
`∂R/∂γ = sigmoid γ - P(first hypothesis | transfer episode)`. -/
theorem hasDerivAt_metaTransferRegret
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    HasDerivAt
      (fun logit =>
        metaTransferRegret logit firstLikelihood secondLikelihood)
      (metaTransferGradient
        structuralLogit firstLikelihood secondLikelihood)
      structuralLogit := by
  have hmixture :
      HasDerivAt
        (fun logit =>
          mixtureLikelihood logit firstLikelihood secondLikelihood)
        (Real.sigmoid structuralLogit *
          (1 - Real.sigmoid structuralLogit) *
          (firstLikelihood - secondLikelihood))
        structuralLogit := by
    have hscaled :=
      (Real.hasDerivAt_sigmoid structuralLogit).mul_const
        (firstLikelihood - secondLikelihood)
    have haffine := hscaled.const_add secondLikelihood
    have hfunction :
        (fun logit =>
          mixtureLikelihood logit firstLikelihood secondLikelihood) =
        fun logit =>
          secondLikelihood +
            Real.sigmoid logit * (firstLikelihood - secondLikelihood) := by
      funext logit
      unfold mixtureLikelihood
      ring
    rw [hfunction]
    exact haffine
  have hnonzero :
      mixtureLikelihood
          structuralLogit firstLikelihood secondLikelihood ≠ 0 :=
    ne_of_gt (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)
  have hregret := (hmixture.log hnonzero).neg
  have hgradient :
      metaTransferGradient
          structuralLogit firstLikelihood secondLikelihood =
        -(Real.sigmoid structuralLogit *
          (1 - Real.sigmoid structuralLogit) *
          (firstLikelihood - secondLikelihood) /
          mixtureLikelihood
            structuralLogit firstLikelihood secondLikelihood) := by
    unfold metaTransferGradient firstHypothesisPosterior
    field_simp [hnonzero]
    unfold mixtureLikelihood
    ring
  rw [hgradient]
  change HasDerivAt
    (fun logit =>
      -Real.log
        (mixtureLikelihood logit firstLikelihood secondLikelihood))
    (-(Real.sigmoid structuralLogit *
      (1 - Real.sigmoid structuralLogit) *
      (firstLikelihood - secondLikelihood) /
      mixtureLikelihood
        structuralLogit firstLikelihood secondLikelihood))
    structuralLogit
  exact hregret

theorem deriv_metaTransferRegret
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    deriv
      (fun logit =>
        metaTransferRegret logit firstLikelihood secondLikelihood)
      structuralLogit =
      metaTransferGradient
        structuralLogit firstLikelihood secondLikelihood :=
  (hasDerivAt_metaTransferRegret
    structuralLogit firstLikelihood secondLikelihood hfirst hsecond).deriv

/-- The structural gradient is a positive scale times the online-likelihood
gap `second - first`. -/
theorem metaTransferGradient_eq_scaled_likelihoodGap
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood) :
    metaTransferGradient
        structuralLogit firstLikelihood secondLikelihood =
      Real.sigmoid structuralLogit *
        (1 - Real.sigmoid structuralLogit) *
        (secondLikelihood - firstLikelihood) /
        mixtureLikelihood
          structuralLogit firstLikelihood secondLikelihood := by
  have hnonzero :
      mixtureLikelihood
          structuralLogit firstLikelihood secondLikelihood ≠ 0 :=
    ne_of_gt (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)
  unfold metaTransferGradient firstHypothesisPosterior
  field_simp [hnonzero]
  unfold mixtureLikelihood
  ring

/-- If the first hypothesis has larger online likelihood, gradient descent
increases its structural logit. -/
theorem metaTransferGradient_neg_of_firstLikelihood_gt
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood)
    (hbetter : secondLikelihood < firstLikelihood) :
    metaTransferGradient
        structuralLogit firstLikelihood secondLikelihood < 0 := by
  rw [metaTransferGradient_eq_scaled_likelihoodGap
    structuralLogit firstLikelihood secondLikelihood hfirst hsecond]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg
      (mul_pos
        (Real.sigmoid_pos structuralLogit)
        (sub_pos.mpr (Real.sigmoid_lt_one structuralLogit)))
      (sub_neg.mpr hbetter))
    (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)

/-- If the second hypothesis has larger online likelihood, gradient descent
decreases the first hypothesis's structural logit. -/
theorem metaTransferGradient_pos_of_secondLikelihood_gt
    (structuralLogit firstLikelihood secondLikelihood : ℝ)
    (hfirst : 0 < firstLikelihood)
    (hsecond : 0 < secondLikelihood)
    (hbetter : firstLikelihood < secondLikelihood) :
    0 < metaTransferGradient
      structuralLogit firstLikelihood secondLikelihood := by
  rw [metaTransferGradient_eq_scaled_likelihoodGap
    structuralLogit firstLikelihood secondLikelihood hfirst hsecond]
  exact div_pos
    (mul_pos
      (mul_pos
        (Real.sigmoid_pos structuralLogit)
        (sub_pos.mpr (Real.sigmoid_lt_one structuralLogit)))
      (sub_pos.mpr hbetter))
    (mixtureLikelihood_pos
      structuralLogit firstLikelihood secondLikelihood hfirst hsecond)

/-- Equal online likelihoods are structurally unidentifiable by this
meta-transfer signal. -/
theorem equalLikelihoods_have_zero_metaTransferGradient
    (structuralLogit likelihood : ℝ)
    (hlikelihood : 0 < likelihood) :
    metaTransferGradient structuralLogit likelihood likelihood = 0 := by
  rw [metaTransferGradient_eq_scaled_likelihoodGap
    structuralLogit likelihood likelihood hlikelihood hlikelihood]
  ring

/-- Concrete nondegenerate signal: equal structural prior, likelihood ratio
three to one, and gradient minus one quarter. -/
theorem threeToOneLikelihood_metaTransferGradient :
    metaTransferGradient 0 3 1 = -(1 / 4 : ℝ) := by
  norm_num [metaTransferGradient, firstHypothesisPosterior,
    mixtureLikelihood, Real.sigmoid_zero]

/-- The positivity premise is load-bearing. With two zero likelihoods the
mixture vanishes, the posterior is an artificial division-by-zero value, and
the real logarithm's totalized value is not a statistical regret. -/
theorem zeroLikelihoods_destroy_metaTransferModel
    (structuralLogit : ℝ) :
    mixtureLikelihood structuralLogit 0 0 = 0 ∧
      metaTransferRegret structuralLogit 0 0 = 0 := by
  simp [mixtureLikelihood, metaTransferRegret]

#print axioms expectedScore_eq_zero_of_matched
#print axioms shifted_distribution_nonzero_expectedScore
#print axioms hasDerivAt_metaTransferRegret
#print axioms deriv_metaTransferRegret
#print axioms metaTransferGradient_eq_scaled_likelihoodGap
#print axioms metaTransferGradient_neg_of_firstLikelihood_gt
#print axioms equalLikelihoods_have_zero_metaTransferGradient
#print axioms zeroLikelihoods_destroy_metaTransferModel

end

end MetaTransferCausalStructure

end Mettapedia.MachineLearning.ContinualLearning
