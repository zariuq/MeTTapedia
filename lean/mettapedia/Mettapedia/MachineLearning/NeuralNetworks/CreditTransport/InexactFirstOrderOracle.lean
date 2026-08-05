import Mathlib.Analysis.Convex.Strong

/-!
# Strongly convex inexact first-order oracles

This file isolates a strongly-convex extension of the `(δ, L)` first-order
oracle of Devolder, Glineur, and Nesterov.
An oracle reports a lower model value and gradient on a convex domain.  Its
error budget appears only in the upper model inequality; the lower inequality
retains the declared strong-convexity modulus.

The central theorem derives the strong-convex affine inequality directly from
the two pointwise oracle inequalities.  Separate endpoint lemmas expose the
one-sided value contract, and exact and biased scalar fixtures show both the
zero-error recovery and why a positive error budget cannot be silently erased.

This is an oracle interface, not a convergence theorem for a particular
optimizer.  Applying it to predictive settling still requires an executable
binding from the recorded value and credit signal to these two inequalities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace InexactFirstOrderOracle

open Set
open scoped InnerProductSpace

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- A proof-carrying `(δ, L, μ)` first-order oracle on `domain`.

`value` is deliberately distinct from `objective`: at positive `δ` the oracle
may return a lower approximation rather than the exact objective value. -/
structure Certificate
    (domain : Set State)
    (objective value : State → ℝ)
    (gradient : State → State)
    (delta smoothness strongConvexity : ℝ) : Prop where
  delta_nonneg : 0 ≤ delta
  strongConvexity_nonneg : 0 ≤ strongConvexity
  strongConvexity_le_smoothness : strongConvexity ≤ smoothness
  lower :
    ∀ x ∈ domain, ∀ y ∈ domain,
      strongConvexity / 2 * ‖x - y‖ ^ 2 ≤
        objective x - (value y + ⟪gradient y, x - y⟫_ℝ)
  upper :
    ∀ x ∈ domain, ∀ y ∈ domain,
      objective x - (value y + ⟪gradient y, x - y⟫_ℝ) ≤
        smoothness / 2 * ‖x - y‖ ^ 2 + delta

/-- Oracle values are lower approximations of the objective on the domain. -/
theorem value_le_objective
    {domain : Set State} {objective value : State → ℝ}
    {gradient : State → State} {delta smoothness strongConvexity : ℝ}
    (oracle :
      Certificate domain objective value gradient
        delta smoothness strongConvexity)
    {state : State} (hstate : state ∈ domain) :
    value state ≤ objective state := by
  have lower := oracle.lower state hstate state hstate
  simpa using lower

/-- The objective exceeds its reported oracle value by at most `delta`. -/
theorem objective_le_value_add_delta
    {domain : Set State} {objective value : State → ℝ}
    {gradient : State → State} {delta smoothness strongConvexity : ℝ}
    (oracle :
      Certificate domain objective value gradient
        delta smoothness strongConvexity)
    {state : State} (hstate : state ∈ domain) :
    objective state ≤ value state + delta := by
  have upper := oracle.upper state hstate state hstate
  simpa [add_comm] using upper

/-- With zero oracle error, the reported value is forced to be exact. -/
theorem value_eq_objective_of_delta_zero
    {domain : Set State} {objective value : State → ℝ}
    {gradient : State → State} {smoothness strongConvexity : ℝ}
    (oracle :
      Certificate domain objective value gradient
        0 smoothness strongConvexity)
    {state : State} (hstate : state ∈ domain) :
    value state = objective state := by
  exact le_antisymm
    (value_le_objective oracle hstate)
    (by simpa using objective_le_value_add_delta oracle hstate)

/-- A strong-convexity consequence of the extended oracle contract:
the oracle value at an affine combination inherits the declared strong
convexity modulus without paying the error budget. -/
theorem value_affine_le
    {domain : Set State} {objective value : State → ℝ}
    {gradient : State → State} {delta smoothness strongConvexity : ℝ}
    (oracle :
      Certificate domain objective value gradient
        delta smoothness strongConvexity)
    (domain_convex : Convex ℝ domain)
    {x y : State} (hx : x ∈ domain) (hy : y ∈ domain)
    {weight : ℝ} (weight_nonneg : 0 ≤ weight)
    (weight_le_one : weight ≤ 1) :
    value (weight • x + (1 - weight) • y) ≤
      (1 - weight) * objective y + weight * objective x -
        strongConvexity / 2 * weight * (1 - weight) * ‖y - x‖ ^ 2 := by
  let center := weight • x + (1 - weight) • y
  have complement_nonneg : 0 ≤ 1 - weight := by linarith
  have weights_sum : weight + (1 - weight) = 1 := by ring
  have hcenter : center ∈ domain :=
    domain_convex hx hy weight_nonneg complement_nonneg weights_sum
  have lower_y := oracle.lower y hy center hcenter
  have lower_x := oracle.lower x hx center hcenter
  have bound_y :
      value center ≤ objective y -
        ⟪gradient center, y - center⟫_ℝ -
        strongConvexity / 2 * ‖y - center‖ ^ 2 := by
    linarith
  have bound_x :
      value center ≤ objective x -
        ⟪gradient center, x - center⟫_ℝ -
        strongConvexity / 2 * ‖x - center‖ ^ 2 := by
    linarith
  have y_sub_center : y - center = weight • (y - x) := by
    dsimp [center]
    module
  have x_sub_center : x - center = (1 - weight) • (x - y) := by
    dsimp [center]
    module
  have norm_xy : ‖x - y‖ = ‖y - x‖ := by
    rw [← norm_neg]
    congr 1
    abel
  have inner_xy :
      ⟪gradient center, x - y⟫_ℝ =
        -⟪gradient center, y - x⟫_ℝ := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  calc
    value center =
        (1 - weight) * value center + weight * value center := by ring
    _ ≤
        (1 - weight) *
            (objective y - ⟪gradient center, y - center⟫_ℝ -
              strongConvexity / 2 * ‖y - center‖ ^ 2) +
          weight *
            (objective x - ⟪gradient center, x - center⟫_ℝ -
              strongConvexity / 2 * ‖x - center‖ ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left bound_y complement_nonneg)
        (mul_le_mul_of_nonneg_left bound_x weight_nonneg)
    _ =
        (1 - weight) * objective y + weight * objective x -
          strongConvexity / 2 * weight * (1 - weight) *
            ‖y - x‖ ^ 2 := by
      rw [y_sub_center, x_sub_center, norm_smul, norm_smul, norm_xy]
      simp only [Real.norm_eq_abs, abs_of_nonneg weight_nonneg,
        abs_of_nonneg complement_nonneg, inner_smul_right]
      rw [inner_xy]
      ring

/-- The objective-level consequence of `value_affine_le`; positive oracle
error is paid once at the queried affine center. -/
theorem objective_affine_le
    {domain : Set State} {objective value : State → ℝ}
    {gradient : State → State} {delta smoothness strongConvexity : ℝ}
    (oracle :
      Certificate domain objective value gradient
        delta smoothness strongConvexity)
    (domain_convex : Convex ℝ domain)
    {x y : State} (hx : x ∈ domain) (hy : y ∈ domain)
    {weight : ℝ} (weight_nonneg : 0 ≤ weight)
    (weight_le_one : weight ≤ 1) :
    objective (weight • x + (1 - weight) • y) ≤
      (1 - weight) * objective y + weight * objective x -
        strongConvexity / 2 * weight * (1 - weight) * ‖y - x‖ ^ 2 +
          delta := by
  let center := weight • x + (1 - weight) • y
  have complement_nonneg : 0 ≤ 1 - weight := by linarith
  have hcenter : center ∈ domain :=
    domain_convex hx hy weight_nonneg complement_nonneg (by ring)
  have hvalue := value_affine_le oracle domain_convex hx hy
    weight_nonneg weight_le_one
  have hobjective := objective_le_value_add_delta oracle hcenter
  dsimp [center] at hobjective ⊢
  linarith

/-! ## Exact and biased scalar witnesses -/

noncomputable def unitQuadratic (state : ℝ) : ℝ := state ^ 2 / 2

/-- The exact value and gradient of the unit quadratic form a zero-error
`(0, 1, 1)` oracle. -/
noncomputable def unitQuadraticCertificate :
    Certificate (Set.univ : Set ℝ) unitQuadratic unitQuadratic id 0 1 1 where
  delta_nonneg := by norm_num
  strongConvexity_nonneg := by norm_num
  strongConvexity_le_smoothness := by norm_num
  lower := by
    intro x _ y _
    simp only [unitQuadratic, id_eq, Real.inner_apply]
    rw [Real.norm_eq_abs, sq_abs]
    ring_nf
    exact le_rfl
  upper := by
    intro x _ y _
    simp only [unitQuadratic, id_eq, Real.inner_apply]
    rw [Real.norm_eq_abs, sq_abs]
    ring_nf
    exact le_rfl

/-- A one-unit lower-biased value is a valid `(1, 0, 0)` oracle for the zero
objective. -/
noncomputable def biasedZeroCertificate :
    Certificate (Set.univ : Set ℝ)
      (fun _ => 0) (fun _ => -1) (fun _ => 0) 1 0 0 where
  delta_nonneg := by norm_num
  strongConvexity_nonneg := by norm_num
  strongConvexity_le_smoothness := by norm_num
  lower := by norm_num
  upper := by norm_num

theorem biasedZero_value_gap_is_one :
    (0 : ℝ) - (fun _ : ℝ => -1) 0 = 1 := by
  norm_num

/-- The same biased report cannot be reclassified as a zero-error oracle,
independently of the advertised smoothness and strong-convexity constants. -/
theorem biasedZero_has_no_exactCertificate
    (smoothness strongConvexity : ℝ) :
    ¬ Certificate (Set.univ : Set ℝ)
      (fun _ => 0) (fun _ => -1) (fun _ => 0)
      0 smoothness strongConvexity := by
  intro oracle
  have exactValue := value_eq_objective_of_delta_zero oracle
    (Set.mem_univ (0 : ℝ))
  norm_num at exactValue

#print axioms value_le_objective
#print axioms objective_le_value_add_delta
#print axioms value_eq_objective_of_delta_zero
#print axioms value_affine_le
#print axioms objective_affine_le
#print axioms unitQuadraticCertificate
#print axioms biasedZeroCertificate
#print axioms biasedZero_has_no_exactCertificate

end InexactFirstOrderOracle

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
