import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-!
# Inexact Moreau-gradient certificates

Lin, Mairal, and Harchaoui, *Catalyst Acceleration for First-order Convex
Optimization* (arXiv:1712.05654), Section 2.3, turn accuracy in a strongly
convex proximal subproblem into an error bound for the approximate Moreau
gradient.  Equation (9) gives the absolute-accuracy bound, while criterion
`(C2)` gives the relative-error form.

This file isolates the reusable content from the surrounding Catalyst
algorithm.  The main statements require only a pointwise quadratic-growth
certificate at the declared minimizer.  They therefore apply to any proximal
or settling subproblem for which that growth certificate is available.

The file also binds the resulting observable radius to the existing
directional task-descent theorem.  Two negative fixtures record why neither
zero growth nor a unit relative-error factor can support the corresponding
conclusions.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace InexactMoreauGradient

open scoped InnerProductSpace

variable {State : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Pointwise quadratic growth of an objective around a declared minimizer.

For a `modulus`-strongly convex objective this follows from optimality at
`minimizer`, but the error theorem below needs only this weaker statement. -/
def HasQuadraticGrowthAt
    (objective : State → ℝ) (minimizer : State) (modulus : ℝ) : Prop :=
  ∀ point,
    modulus / 2 * ‖point - minimizer‖ ^ 2 ≤
      objective point - objective minimizer

/-- An approximate point is within `accuracy` in objective value of the
declared minimizer.  This is Catalyst's absolute criterion `(C1)` after the
proximal objective has been fixed. -/
def WithinValueAccuracy
    (objective : State → ℝ) (minimizer point : State) (accuracy : ℝ) : Prop :=
  objective point - objective minimizer ≤ accuracy

/-- The gradient surrogate obtained by replacing the exact proximal point by
an approximate point. -/
def approximateMoreauGradient
    (modulus : ℝ) (center point : State) : State :=
  modulus • (center - point)

/-- Observable error radius associated with value accuracy. -/
noncomputable def valueAccuracyErrorRadius
    (modulus accuracy : ℝ) : ℝ :=
  Real.sqrt (2 * modulus * accuracy)

omit [NormedSpace ℝ State] in
/-- Quadratic growth plus value accuracy bounds the squared distance to the
declared minimizer.  This is the metric core of Catalyst Equation (9), stated
without introducing a square root. -/
theorem valueAccuracy_distance_sq_le
    {objective : State → ℝ} {minimizer point : State}
    {modulus accuracy : ℝ}
    (growth : HasQuadraticGrowthAt objective minimizer modulus)
    (certificate :
      WithinValueAccuracy objective minimizer point accuracy) :
    modulus * ‖point - minimizer‖ ^ 2 ≤ 2 * accuracy := by
  have hgrowth := growth point
  unfold WithinValueAccuracy at certificate
  nlinarith

/-- The difference between approximate and exact Moreau gradients is the
scaled proximal-point error; the proximal center cancels exactly. -/
theorem approximateMoreauGradient_sub
    (modulus : ℝ) (center point minimizer : State) :
    approximateMoreauGradient modulus center point -
        approximateMoreauGradient modulus center minimizer =
      modulus • (minimizer - point) := by
  simp only [approximateMoreauGradient]
  module

/-- Catalyst Equation (9), in squared form:
`‖g(point) - g(minimizer)‖² ≤ 2 * modulus * accuracy`. -/
theorem approximateMoreauGradient_error_sq_le
    {objective : State → ℝ} {minimizer point center : State}
    {modulus accuracy : ℝ}
    (hmodulus : 0 ≤ modulus)
    (growth : HasQuadraticGrowthAt objective minimizer modulus)
    (certificate :
      WithinValueAccuracy objective minimizer point accuracy) :
    ‖approximateMoreauGradient modulus center point -
        approximateMoreauGradient modulus center minimizer‖ ^ 2 ≤
      2 * modulus * accuracy := by
  have hdistance := valueAccuracy_distance_sq_le growth certificate
  have hscaled := mul_le_mul_of_nonneg_left hdistance hmodulus
  have hnorm :
      ‖minimizer - point‖ = ‖point - minimizer‖ := by
    rw [show minimizer - point = -(point - minimizer) by abel, norm_neg]
  rw [approximateMoreauGradient_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hmodulus, hnorm]
  nlinarith

/-- Square-root presentation of the absolute-accuracy certificate. -/
theorem approximateMoreauGradient_error_le_radius
    {objective : State → ℝ} {minimizer point center : State}
    {modulus accuracy : ℝ}
    (hmodulus : 0 ≤ modulus)
    (growth : HasQuadraticGrowthAt objective minimizer modulus)
    (certificate :
      WithinValueAccuracy objective minimizer point accuracy) :
    ‖approximateMoreauGradient modulus center point -
        approximateMoreauGradient modulus center minimizer‖ ≤
      valueAccuracyErrorRadius modulus accuracy := by
  have hsquared :=
    approximateMoreauGradient_error_sq_le
      (center := center) hmodulus growth certificate
  have hsqrt := Real.sqrt_le_sqrt hsquared
  rw [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  exact hsqrt

omit [NormedSpace ℝ State] in
/-- A relative proximal-point certificate with factor strictly below one can
be solved for an error bound relative to the exact center-to-minimizer
distance.  This is the triangle-inequality step behind Catalyst criterion
`(C2)`. -/
theorem relative_distance_le
    (center point minimizer : State) (ratio : ℝ)
    (hratioNonneg : 0 ≤ ratio) (hratioLt : ratio < 1)
    (hrelative :
      ‖point - minimizer‖ ≤ ratio * ‖center - point‖) :
    ‖point - minimizer‖ ≤
      ratio * ‖center - minimizer‖ / (1 - ratio) := by
  have htriangle :
      ‖center - point‖ ≤
        ‖center - minimizer‖ + ‖point - minimizer‖ := by
    calc
      ‖center - point‖ =
          ‖(center - minimizer) + (minimizer - point)‖ := by
        congr 1
        abel
      _ ≤ ‖center - minimizer‖ + ‖minimizer - point‖ :=
        norm_add_le _ _
      _ = ‖center - minimizer‖ + ‖point - minimizer‖ := by
        rw [show minimizer - point = -(point - minimizer) by abel,
          norm_neg]
  have hcombined :
      ‖point - minimizer‖ ≤
        ratio * (‖center - minimizer‖ + ‖point - minimizer‖) :=
    hrelative.trans
      (mul_le_mul_of_nonneg_left htriangle hratioNonneg)
  apply (le_div_iff₀ (sub_pos.mpr hratioLt)).2
  nlinarith

/-- Relative proximal-point accuracy implies relative approximate-gradient
accuracy with factor `ratio / (1 - ratio)`.  Catalyst uses
`ratio = sqrt δ`. -/
theorem relativeMoreauGradient_error_le
    (modulus : ℝ) (center point minimizer : State) (ratio : ℝ)
    (hmodulus : 0 ≤ modulus)
    (hratioNonneg : 0 ≤ ratio) (hratioLt : ratio < 1)
    (hrelative :
      ‖point - minimizer‖ ≤ ratio * ‖center - point‖) :
    ‖approximateMoreauGradient modulus center point -
        approximateMoreauGradient modulus center minimizer‖ ≤
      ratio *
          ‖approximateMoreauGradient modulus center minimizer‖ /
        (1 - ratio) := by
  have hdistance :=
    relative_distance_le center point minimizer ratio
      hratioNonneg hratioLt hrelative
  have hnorm :
      ‖minimizer - point‖ = ‖point - minimizer‖ := by
    rw [show minimizer - point = -(point - minimizer) by abel, norm_neg]
  rw [approximateMoreauGradient_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hmodulus, hnorm, approximateMoreauGradient, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hmodulus]
  have hscaled := mul_le_mul_of_nonneg_left hdistance hmodulus
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hscaled

/-! ## Binding to approximate-credit descent -/

section InnerProduct

variable {HilbertState : Type*}
  [NormedAddCommGroup HilbertState] [InnerProductSpace ℝ HilbertState]

/-- An observable value-accuracy gate can certify that the approximate
Moreau gradient remains positively aligned with the exact one. -/
theorem valueAccuracy_positive_alignment
    {objective : HilbertState → ℝ}
    {minimizer point center : HilbertState}
    {modulus accuracy : ℝ}
    (hmodulus : 0 ≤ modulus)
    (growth : HasQuadraticGrowthAt objective minimizer modulus)
    (certificate :
      WithinValueAccuracy objective minimizer point accuracy)
    (hgate :
      2 * modulus * accuracy <
        ‖approximateMoreauGradient modulus center minimizer‖ ^ 2) :
    0 <
      ⟪approximateMoreauGradient modulus center minimizer,
        approximateMoreauGradient modulus center point⟫_ℝ := by
  let exact := approximateMoreauGradient modulus center minimizer
  let approximate := approximateMoreauGradient modulus center point
  have hsquared :
      ‖approximate - exact‖ ^ 2 ≤ 2 * modulus * accuracy := by
    simpa [exact, approximate] using
      approximateMoreauGradient_error_sq_le
        (center := center) hmodulus growth certificate
  have herrorSq :
      ‖approximate - exact‖ ^ 2 < ‖exact‖ ^ 2 :=
    lt_of_le_of_lt hsquared hgate
  have hrelative :
      ‖approximate - exact‖ < ‖exact‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp herrorSq
  have hlower :=
    DirectionalTaskDescent.approximateDirection_inner_lower
      exact approximate ‖approximate - exact‖ (le_refl _)
  have hexactPositive : 0 < ‖exact‖ :=
    lt_of_le_of_lt (norm_nonneg _) hrelative
  have hmargin :
      0 < ‖exact‖ * (‖exact‖ - ‖approximate - exact‖) :=
    mul_pos hexactPositive (sub_pos.mpr hrelative)
  dsimp [exact, approximate] at hlower ⊢
  linarith

/-- The Catalyst value-gap radius can be supplied directly to the existing
smooth-task finite-step certificate.  This theorem certifies task descent; it
does not infer the smooth upper model or the quadratic-growth premise from
runtime traces. -/
theorem valueAccuracy_smoothTask_strict_descent
    {proximalObjective taskLoss : HilbertState → ℝ}
    {minimizer point center parameter : HilbertState}
    {modulus accuracy beta step : ℝ}
    (hmodulus : 0 ≤ modulus)
    (growth :
      HasQuadraticGrowthAt proximalObjective minimizer modulus)
    (valueCertificate :
      WithinValueAccuracy proximalObjective minimizer point accuracy)
    (taskCertificate :
      DirectionalTaskDescent.HasSmoothTaskUpperModelAt
        taskLoss parameter
          (approximateMoreauGradient modulus center minimizer) beta)
    (hbeta : 0 ≤ beta) (hstep : 0 < step)
    (hrelative :
      valueAccuracyErrorRadius modulus accuracy <
        ‖approximateMoreauGradient modulus center minimizer‖)
    (htrust :
      beta * step *
            (‖approximateMoreauGradient modulus center minimizer‖ +
              valueAccuracyErrorRadius modulus accuracy) ^ 2 /
            2 <
        ‖approximateMoreauGradient modulus center minimizer‖ *
          (‖approximateMoreauGradient modulus center minimizer‖ -
            valueAccuracyErrorRadius modulus accuracy)) :
    taskLoss
        (parameter -
          step • approximateMoreauGradient modulus center point) <
      taskLoss parameter := by
  apply
    DirectionalTaskDescent.smoothTask_strict_descent_of_norm_error
      taskCertificate
      (approximateMoreauGradient_error_le_radius
        hmodulus growth valueCertificate)
      hbeta hstep hrelative htrust

end InnerProduct

/-! ## Positive and negative fixtures -/

/-- A scalar quadratic objective realizing the growth bound exactly. -/
noncomputable def scalarQuadratic
    (modulus minimizer point : ℝ) : ℝ :=
  modulus / 2 * (point - minimizer) ^ 2

/-- The scalar quadratic has the declared pointwise quadratic growth. -/
theorem scalarQuadratic_hasQuadraticGrowth
    (modulus minimizer : ℝ) :
    HasQuadraticGrowthAt
      (scalarQuadratic modulus minimizer) minimizer modulus := by
  intro point
  simp [scalarQuadratic, Real.norm_eq_abs, sq_abs]

/-- Equation (9)'s squared gradient-error bound is attained by a nonzero
one-dimensional fixture. -/
theorem scalar_valueAccuracy_gradient_bound_is_sharp :
    WithinValueAccuracy (scalarQuadratic 1 0) 0 1 (1 / 2) ∧
    ‖approximateMoreauGradient 1 (3 : ℝ) 1 -
        approximateMoreauGradient 1 (3 : ℝ) 0‖ ^ 2 =
      2 * 1 * (1 / 2 : ℝ) := by
  constructor
  · norm_num [WithinValueAccuracy, scalarQuadratic]
  · norm_num [approximateMoreauGradient, Real.norm_eq_abs]

/-- At relative factor one, the premise can hold while the exact Moreau
gradient is zero and the approximate-gradient error is nonzero.  Hence the
strict `ratio < 1` boundary cannot be removed. -/
theorem unit_relative_ratio_is_not_a_gradient_error_certificate :
    ‖(1 : ℝ) - 0‖ ≤ 1 * ‖(0 : ℝ) - 1‖ ∧
    ‖approximateMoreauGradient 1 (0 : ℝ) 1 -
        approximateMoreauGradient 1 (0 : ℝ) 0‖ = 1 ∧
    approximateMoreauGradient 1 (0 : ℝ) 0 = 0 := by
  norm_num [approximateMoreauGradient, Real.norm_eq_abs]

/-- With zero growth, exact value accuracy for a constant objective places no
finite bound on the distance to the declared minimizer. -/
theorem zero_growth_value_accuracy_has_unbounded_distance :
    HasQuadraticGrowthAt (fun _ : ℝ => 0) 0 0 ∧
    ∀ bound : ℝ, 0 ≤ bound →
      ∃ point : ℝ,
        WithinValueAccuracy (fun _ : ℝ => 0) 0 point 0 ∧
          bound < ‖point - 0‖ := by
  constructor
  · intro point
    norm_num
  · intro bound hbound
    refine ⟨bound + 1, ?_, ?_⟩
    · norm_num [WithinValueAccuracy]
    · rw [sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ bound + 1)]
      linarith

#print axioms valueAccuracy_distance_sq_le
#print axioms approximateMoreauGradient_error_sq_le
#print axioms relativeMoreauGradient_error_le
#print axioms valueAccuracy_positive_alignment
#print axioms valueAccuracy_smoothTask_strict_descent
#print axioms scalar_valueAccuracy_gradient_bound_is_sharp
#print axioms unit_relative_ratio_is_not_a_gradient_error_certificate
#print axioms zero_growth_value_accuracy_has_unbounded_distance

end InexactMoreauGradient

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
