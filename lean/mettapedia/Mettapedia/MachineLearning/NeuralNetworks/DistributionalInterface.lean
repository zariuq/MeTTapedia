import Mettapedia.Logic.WorldModel.DistributionalSpace
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.LogitLossCurvature
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator

/-!
# Neural likelihoods and distributional spaces

A real-valued logit parameterizes a normalized observation channel. Its loss
and the evidence objective are derived from those probabilities. Parameter
sharing does not specify random-choice sharing. Gaussian predictive coding
is a separate measure-valued interpretation, retaining its covariance.
-/
set_option autoImplicit false

namespace Mettapedia.MachineLearning.NeuralNetworks.DistributionalInterface
open Finset Mettapedia.InformationTheory Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Logic.DistributionalSpace
open Mettapedia.InformationTheory.FiniteRV
open CreditTransport.LogitLossCurvature

noncomputable def bernoulli (logit : ℝ) : Prob Bool :=
  ⟨fun b => if b then Real.sigmoid logit else Real.sigmoid (-logit),
    fun b => by cases b <;> simp [Real.sigmoid_nonneg], by
      simp [Real.sigmoid_neg]⟩

theorem log_sigmoid (z : ℝ) :
    Real.log (Real.sigmoid z) = z - Real.log (1 + Real.exp z) := by
  have heq : Real.sigmoid z = Real.exp z / (1 + Real.exp z) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp
    ring
  rw [heq, Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp]

/-- Both outcomes' negative log likelihood is binary cross entropy. -/
theorem bernoulli_nll (z : ℝ) (b : Bool) :
    -Real.log ((bernoulli z).1 b) =
      binaryCrossEntropyWithLogits (if b then 1 else 0) z := by
  cases b
  · simp [bernoulli, Real.sigmoid_def, Real.log_inv, binaryCrossEntropyWithLogits]
  · simp only [bernoulli, if_true, log_sigmoid, binaryCrossEntropyWithLogits, one_mul]
    ring

theorem bernoulli_nll_derivative {f : ℝ → ℝ} {f' t : ℝ}
    (h : HasDerivAt f f' t) (b : Bool) :
    HasDerivAt (fun x => -Real.log ((bernoulli (f x)).1 b))
      ((Real.sigmoid (f t) - if b then 1 else 0) * f') t := by
  simp_rw [bernoulli_nll]
  exact (hasDerivAt_binaryCrossEntropyWithLogits _ _).comp t h

/-- A trainable affine observation channel. Latent features and report identity
are explicit inputs; channel independence is supplied separately by the model. -/
noncomputable def affineChannel {Ω Id : Type*} (feature : Id → Ω → ℝ)
    (bias : Id → ℝ) (θ : ℝ) (w : Ω) (i : Id) : Prob Bool :=
  bernoulli (θ * feature i w + bias i)

theorem affineChannel_loss_derivative {Ω Id : Type*} (feature : Id → Ω → ℝ)
    (bias : Id → ℝ) (θ : ℝ) (w : Ω) (i : Id) (b : Bool) :
    HasDerivAt (fun t => -Real.log ((affineChannel feature bias t w i).1 b))
      ((Real.sigmoid (θ * feature i w + bias i) - if b then 1 else 0) * feature i w) θ := by
  simpa only [affineChannel, id_eq, one_mul] using
    bernoulli_nll_derivative (((hasDerivAt_id θ).mul_const (feature i w)).add_const (bias i)) b

section Finite
variable {Ω O Id Θ : Type*} [Fintype Ω] [Fintype O]

/-- The Space's supplied likelihood, not an unrelated optimizing distribution,
induces the existing variational functional. -/
theorem space_variational (m : Model Θ Ω O Id) (θ : Θ) (E : Finset Id)
    (q : Prob Ω) (h : 0 < m.normalizer θ E)
    (support : SupportedBy q (fun w => (m.prior θ).1 w * m.likelihood θ E w)) :
    variationalFreeEnergy (m.prior θ) (m.likelihood θ E) q =
      klSum q.1 (posterior (m.prior θ) (m.likelihood θ E)
        (m.likelihood_nonneg θ E) h).1 - Real.log (m.normalizer θ E) :=
  variationalFreeEnergy_eq _ _ _ _ h support

/-- Fisher's score identity for a finite latent space. The scalar argument can
be any parameter path, in particular `θ + t • v` for a directional derivative.
The prior is fixed; a trainable prior needs its own score term. -/
theorem evidence_score (prior : Prob Ω) (L : ℝ → Ω → ℝ) (dL : Ω → ℝ) (t : ℝ)
    (derivative : ∀ w, HasDerivAt (fun x => L x w) (dL w) t)
    (positive : ∀ w, 0 < L t w) (possible : 0 < evidence prior (L t)) :
    HasDerivAt (fun x => -Real.log (evidence prior (L x)))
      (-(∑ w, (posterior prior (L t) (fun w => (positive w).le) possible).1 w *
        (dL w / L t w))) t := by
  have hd : HasDerivAt (fun x => evidence prior (L x)) (∑ w, prior.1 w * dL w) t :=
    HasDerivAt.fun_sum fun w _ => (derivative w).const_mul (prior.1 w)
  apply ((hd.log possible.ne').neg).congr_deriv
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  rw [posterior_apply]
  field_simp [(positive w).ne']

omit [Fintype Ω] in
/-- The summands in the score identity are actual derivatives of log likelihood. -/
theorem log_likelihood_derivative (L : ℝ → Ω → ℝ) (dL : Ω → ℝ) (t : ℝ)
    (derivative : ∀ w, HasDerivAt (fun x => L x w) (dL w) t)
    (positive : ∀ w, 0 < L t w) (w : Ω) :
    HasDerivAt (fun x => Real.log (L x w)) (dL w / L t w) t :=
  (derivative w).log (positive w).ne'

/-- The score identity for an actual Space along a parameter path. Choosing
`path t = θ + t • v` gives a directional derivative in any parameter space. -/
theorem space_score_along (m : Model Θ Ω O Id) (path : ℝ → Θ) (prior : Prob Ω)
    (fixed : ∀ t, m.prior (path t) = prior) (E : Finset Id) (t : ℝ) (dL : Ω → ℝ)
    (derivative : ∀ w, HasDerivAt (fun x => m.likelihood (path x) E w) (dL w) t)
    (positive : ∀ w, 0 < m.likelihood (path t) E w)
    (possible : 0 < evidence prior (m.likelihood (path t) E)) :
    HasDerivAt (fun x => -Real.log (m.normalizer (path x) E))
      (-(∑ w, (posterior prior (m.likelihood (path t) E)
          (fun w => (positive w).le) possible).1 w *
        (dL w / m.likelihood (path t) E w))) t := by
  simp only [Model.normalizer, fixed]
  exact evidence_score prior (fun x => m.likelihood (path x) E) dL t derivative positive possible

end Finite

section Gaussian
open PredictiveCoding _root_.ProbabilityTheory MeasureTheory
variable {Latent Residual : Type*} [Fintype Latent] [DecidableEq Latent]
  [Fintype Residual] [DecidableEq Residual]

/-- Equilibrium retains a distribution-valued interpretation and its mean law. -/
theorem gaussian_equilibrium_mean (m : LinearGaussianOperatorModel Latent Residual)
    (u : LinearGaussianOperatorSpace Latent) :
    m.Equilibrium u ↔ u = ∫ v, v ∂m.posterior :=
  m.equilibrium_iff_eq_conditionalPosteriorMean u

/-- Every latent coordinate has positive posterior variance. -/
theorem gaussian_variance_positive (m : LinearGaussianOperatorModel Latent Residual)
    (i : Latent) : 0 < variance (fun v => v i) m.posterior := by
  rw [LinearGaussianOperatorModel.posterior,
    variance_eval_multivariateGaussian m.posterior_covariance_posDef.posSemidef]
  exact m.posterior_covariance_posDef.diag_pos

/-- Replacing the posterior by its mean discards a query even at equilibrium. -/
theorem gaussian_not_mean_dirac (m : LinearGaussianOperatorModel Latent Residual)
    (i : Latent) : m.posterior ≠ Measure.dirac m.posteriorMean := by
  intro h
  have hv := gaussian_variance_positive m i
  rw [h, variance_dirac] at hv
  exact (lt_irrefl 0) hv

end Gaussian
end Mettapedia.MachineLearning.NeuralNetworks.DistributionalInterface
