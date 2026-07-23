import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalLinearizationCertificate

/-!
# Local existence of regional gradient certificates

A strict positive margin at one audited linearization is not by itself a
numerical regional certificate.  If the gradient Jacobian is continuous,
however, some nonzero closed ball inherits a uniform Jacobian-deviation
budget.  This module proves that local existence result while keeping the
radius existential: extracting a useful radius for an implementation still
requires a quantitative enclosure.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace LocalRegionalCertificateExistence

open scoped InnerProductSpace
open AmortizedInitialization
open RegionalLinearizationCertificate

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- Continuity of the Jacobian turns a strict positive central margin into a
uniform enclosure on some nonzero closed ball.  The theorem is deliberately
existential in the radius; a sampled point estimate does not determine it. -/
theorem exists_local_regionalGradientJacobianEnclosure
    (gradient : State → State) (center : State)
    (linear : State →L[ℝ] State) (modulus : ℝ)
    (hmodulus : 0 < modulus)
    (hdifferentiable : ∀ state, DifferentiableAt ℝ gradient state)
    (hcontinuous :
      ContinuousAt (fun state => fderiv ℝ gradient state) center)
    (hlinear : linear = fderiv ℝ gradient center)
    (hstationary : gradient center = 0)
    (hmodulus_le_norm : modulus ≤ ‖linear‖)
    (hstrong : ∀ displacement,
      modulus * ‖displacement‖ ^ 2 ≤
        ⟪linear displacement, displacement⟫_ℝ) :
    ∃ radius : ℝ, 0 < radius ∧
      Nonempty (RegionalGradientJacobianEnclosure
        gradient center radius linear) := by
  obtain ⟨delta, hdelta, hjacobian⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous)
      (modulus / 2) (by linarith)
  refine ⟨delta / 2, by linarith, ⟨{
    linearModulus := modulus
    jacobianVariation := modulus / 2
    radius_nonneg := by linarith
    linearModulus_nonneg := hmodulus.le
    jacobianVariation_nonneg := by linarith
    jacobianVariation_lt_linearModulus := by linarith
    linearModulus_le_norm := hmodulus_le_norm
    gradient_center_zero := hstationary
    gradient_differentiable_on_ball := ?_
    linear_eq_centerJacobian := hlinear
    linear_strongMonotone := hstrong
    jacobian_deviation_on_ball := ?_
  }⟩⟩
  · intro state _
    exact hdifferentiable state
  · intro state hstate
    have hdist : dist state center < delta := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hstate (by linarith)
    have hbound := hjacobian hdist
    simpa [dist_eq_norm, hlinear] using hbound.le

/-! ## Positive and negative boundaries -/

/-- The scalar identity field has an explicit positive regional enclosure on
every nonnegative-radius ball. -/
noncomputable def scalarIdentityEnclosure (radius : ℝ) (hradius : 0 ≤ radius) :
    RegionalGradientJacobianEnclosure
      (fun state : ℝ => state) 0 radius
      (ContinuousLinearMap.id ℝ ℝ) where
  linearModulus := 1
  jacobianVariation := 0
  radius_nonneg := hradius
  linearModulus_nonneg := by norm_num
  jacobianVariation_nonneg := by norm_num
  jacobianVariation_lt_linearModulus := by norm_num
  linearModulus_le_norm := by
    rw [ContinuousLinearMap.norm_id]
  gradient_center_zero := rfl
  gradient_differentiable_on_ball := by
    intro state _
    fun_prop
  linear_eq_centerJacobian := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).fderiv).symm
  linear_strongMonotone := by
    intro displacement
    simp
  jacobian_deviation_on_ball := by
    intro state _
    have hderiv :
        fderiv ℝ (fun candidate : ℝ => candidate) state =
          ContinuousLinearMap.id ℝ ℝ := by
      exact (hasFDerivAt_id state).fderiv
    simp [hderiv]

/-- A zero linearization cannot masquerade as having a positive
strong-monotonicity modulus, even in one dimension. -/
theorem zeroLinear_has_no_positive_modulus :
    ¬ ∃ modulus : ℝ, 0 < modulus ∧
      ∀ displacement : ℝ,
        modulus * ‖displacement‖ ^ 2 ≤
          ⟪(0 : ℝ →L[ℝ] ℝ) displacement, displacement⟫_ℝ := by
  rintro ⟨modulus, hmodulus, hstrong⟩
  have h := hstrong 1
  norm_num [Real.inner_apply] at h
  linarith

#print axioms exists_local_regionalGradientJacobianEnclosure
#print axioms scalarIdentityEnclosure
#print axioms zeroLinear_has_no_positive_modulus

end

end LocalRegionalCertificateExistence

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
