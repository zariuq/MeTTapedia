import Mathlib.Tactic

/-!
# Finite metric and curvature transport through depth

Poole, Lahiri, Raghu, Sohl-Dickstein, and Ganguli,
*Exponential Expressivity in Deep Neural Networks through Transient Chaos*
(arXiv:1606.05340), Equation (8), give mean-field recurrences for the
renormalized Euclidean metric and squared extrinsic curvature of a propagated
curve:

`gₗ = χ₁ gₗ₋₁`,

`κₗ² = 3 χ₂ / χ₁² + κₗ₋₁² / χ₁`.

This file treats those recurrences as an exact finite dynamical system.  It
proves the closed form for the Euclidean metric, the curvature fixed point and
its exact finite-depth error, and an exact product law for the Gauss metric
`κ² g`.  Positive curvature injection makes that product strictly increase at
every layer with positive metric.  With zero injection the same product is
exactly constant, even if the Euclidean metric itself expands.

The source's random-network ensemble, Gaussian mean-field limit, derivation of
`χ₁` and `χ₂` from an activation, manifold convergence, shallow-network lower
bound, classification-boundary curvature, and empirical simulations are not
formalized here.  Runtime use requires measured or otherwise certified
stretch and curvature-injection coefficients.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace TransientChaosGeometry

noncomputable section

/-- Renormalized Euclidean metric after a finite number of layers. -/
def euclideanMetric (stretch initialMetric : ℝ) : ℕ → ℝ
  | 0 => initialMetric
  | depth + 1 => stretch * euclideanMetric stretch initialMetric depth

/-- The additive squared-curvature contribution from one nonlinear layer. -/
def curvatureInjection (stretch curvatureSource : ℝ) : ℝ :=
  3 * curvatureSource / stretch ^ 2

/-- Renormalized squared extrinsic curvature after finite depth. -/
def curvatureSq
    (stretch curvatureSource initialCurvatureSq : ℝ) : ℕ → ℝ
  | 0 => initialCurvatureSq
  | depth + 1 =>
      curvatureInjection stretch curvatureSource +
        curvatureSq stretch curvatureSource initialCurvatureSq depth / stretch

/-- Product metric corresponding to squared curvature times Euclidean metric. -/
def gaussMetric
    (stretch curvatureSource initialMetric initialCurvatureSq : ℝ)
    (depth : ℕ) : ℝ :=
  curvatureSq stretch curvatureSource initialCurvatureSq depth *
    euclideanMetric stretch initialMetric depth

@[simp] theorem euclideanMetric_zero
    (stretch initialMetric : ℝ) :
    euclideanMetric stretch initialMetric 0 = initialMetric := rfl

@[simp] theorem euclideanMetric_succ
    (stretch initialMetric : ℝ) (depth : ℕ) :
    euclideanMetric stretch initialMetric (depth + 1) =
      stretch * euclideanMetric stretch initialMetric depth := rfl

@[simp] theorem curvatureSq_zero
    (stretch curvatureSource initialCurvatureSq : ℝ) :
    curvatureSq stretch curvatureSource initialCurvatureSq 0 =
      initialCurvatureSq := rfl

@[simp] theorem curvatureSq_succ
    (stretch curvatureSource initialCurvatureSq : ℝ) (depth : ℕ) :
    curvatureSq stretch curvatureSource initialCurvatureSq (depth + 1) =
      curvatureInjection stretch curvatureSource +
        curvatureSq stretch curvatureSource initialCurvatureSq depth /
          stretch := rfl

/-- Exact exponential finite-depth solution for the Euclidean metric. -/
theorem euclideanMetric_eq_pow_mul
    (stretch initialMetric : ℝ) (depth : ℕ) :
    euclideanMetric stretch initialMetric depth =
      stretch ^ depth * initialMetric := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [euclideanMetric_succ, ih, pow_succ']
      ring

/-- Positive stretch preserves positivity of the Euclidean metric. -/
theorem euclideanMetric_pos
    (stretch initialMetric : ℝ)
    (hstretch : 0 < stretch) (hinitial : 0 < initialMetric)
    (depth : ℕ) :
    0 < euclideanMetric stretch initialMetric depth := by
  rw [euclideanMetric_eq_pow_mul]
  exact mul_pos (pow_pos hstretch depth) hinitial

/-- In the chaotic regime, every additional layer strictly expands a positive
Euclidean metric. -/
theorem euclideanMetric_succ_strictly_increases
    (stretch initialMetric : ℝ)
    (hstretch : 1 < stretch) (hinitial : 0 < initialMetric)
    (depth : ℕ) :
    euclideanMetric stretch initialMetric depth <
      euclideanMetric stretch initialMetric (depth + 1) := by
  rw [euclideanMetric_succ]
  have hmetric :
      0 < euclideanMetric stretch initialMetric depth :=
    euclideanMetric_pos stretch initialMetric (by linarith) hinitial depth
  nlinarith

/-- Fixed point of the squared-curvature recurrence when `stretch ≠ 0, 1`. -/
def curvatureSqFixedPoint (stretch curvatureSource : ℝ) : ℝ :=
  3 * curvatureSource / (stretch * (stretch - 1))

/-- The declared curvature fixed point is exactly fixed by one recurrence
step. -/
theorem curvatureSqFixedPoint_is_fixed
    (stretch curvatureSource : ℝ)
    (hstretchZero : stretch ≠ 0) (hstretchOne : stretch ≠ 1) :
    curvatureInjection stretch curvatureSource +
        curvatureSqFixedPoint stretch curvatureSource / stretch =
      curvatureSqFixedPoint stretch curvatureSource := by
  unfold curvatureInjection curvatureSqFixedPoint
  field_simp
  ring

/-- Exact finite-depth contraction or expansion of curvature error around the
fixed point. -/
theorem curvatureSq_sub_fixedPoint_eq
    (stretch curvatureSource initialCurvatureSq : ℝ)
    (hstretchZero : stretch ≠ 0) (hstretchOne : stretch ≠ 1)
    (depth : ℕ) :
    curvatureSq stretch curvatureSource initialCurvatureSq depth -
        curvatureSqFixedPoint stretch curvatureSource =
      (1 / stretch) ^ depth *
        (initialCurvatureSq -
          curvatureSqFixedPoint stretch curvatureSource) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      have hfixed :=
        curvatureSqFixedPoint_is_fixed
          stretch curvatureSource hstretchZero hstretchOne
      rw [curvatureSq_succ]
      calc
        curvatureInjection stretch curvatureSource +
              curvatureSq stretch curvatureSource initialCurvatureSq depth /
                stretch -
            curvatureSqFixedPoint stretch curvatureSource =
            (curvatureSq stretch curvatureSource initialCurvatureSq depth -
              curvatureSqFixedPoint stretch curvatureSource) / stretch := by
                field_simp [hstretchZero] at hfixed ⊢
                nlinarith
        _ = ((1 / stretch) ^ depth *
              (initialCurvatureSq -
                curvatureSqFixedPoint stretch curvatureSource)) /
              stretch := by rw [ih]
        _ = (1 / stretch) ^ (depth + 1) *
              (initialCurvatureSq -
                curvatureSqFixedPoint stretch curvatureSource) := by
              rw [pow_succ]
              ring

/-- Nonnegative data remain nonnegative under positive stretch. -/
theorem curvatureSq_nonneg
    (stretch curvatureSource initialCurvatureSq : ℝ)
    (hstretch : 0 < stretch) (hsource : 0 ≤ curvatureSource)
    (hinitial : 0 ≤ initialCurvatureSq) (depth : ℕ) :
    0 ≤ curvatureSq stretch curvatureSource initialCurvatureSq depth := by
  have hinjection :
      0 ≤ curvatureInjection stretch curvatureSource := by
    unfold curvatureInjection
    positivity
  induction depth with
  | zero => simpa
  | succ depth ih =>
      rw [curvatureSq_succ]
      exact add_nonneg hinjection (div_nonneg ih (le_of_lt hstretch))

/-- Exact layerwise product law.  The inherited curvature term cancels the
metric stretch; only newly injected curvature increases the Gauss metric. -/
theorem gaussMetric_succ
    (stretch curvatureSource initialMetric initialCurvatureSq : ℝ)
    (hstretch : stretch ≠ 0) (depth : ℕ) :
    gaussMetric stretch curvatureSource initialMetric initialCurvatureSq
        (depth + 1) =
      gaussMetric stretch curvatureSource initialMetric initialCurvatureSq
          depth +
        (3 * curvatureSource / stretch) *
          euclideanMetric stretch initialMetric depth := by
  unfold gaussMetric
  rw [curvatureSq_succ, euclideanMetric_succ]
  unfold curvatureInjection
  field_simp
  ring

/-- Positive nonlinear curvature injection makes the Gauss metric strictly
increase at every layer with positive initial metric. -/
theorem gaussMetric_succ_strictly_increases
    (stretch curvatureSource initialMetric initialCurvatureSq : ℝ)
    (hstretch : 0 < stretch) (hsource : 0 < curvatureSource)
    (hinitialMetric : 0 < initialMetric) (depth : ℕ) :
    gaussMetric stretch curvatureSource initialMetric initialCurvatureSq
        depth <
      gaussMetric stretch curvatureSource initialMetric initialCurvatureSq
        (depth + 1) := by
  rw [gaussMetric_succ stretch curvatureSource initialMetric
    initialCurvatureSq (ne_of_gt hstretch)]
  have hcoefficient : 0 < 3 * curvatureSource / stretch := by
    positivity
  have hmetric :
      0 < euclideanMetric stretch initialMetric depth :=
    euclideanMetric_pos stretch initialMetric hstretch hinitialMetric depth
  nlinarith [mul_pos hcoefficient hmetric]

/-- With zero curvature injection, the Gauss metric is exactly conserved at
all finite depths.  Linear stretching alone therefore does not create this
global curvature measure. -/
theorem gaussMetric_zero_curvatureSource
    (stretch initialMetric initialCurvatureSq : ℝ)
    (hstretch : stretch ≠ 0) (depth : ℕ) :
    gaussMetric stretch 0 initialMetric initialCurvatureSq depth =
      initialCurvatureSq * initialMetric := by
  induction depth with
  | zero => simp [gaussMetric]
  | succ depth ih =>
      rw [gaussMetric_succ stretch 0 initialMetric initialCurvatureSq
        hstretch, ih]
      ring

/-- A concrete positive-injection trajectory: at stretch two, source one,
and unit initial data, the Gauss metric grows from `1` to `5/2` to `11/2`. -/
theorem stretchTwo_positiveInjection :
    gaussMetric 2 1 1 1 0 = 1 ∧
      gaussMetric 2 1 1 1 1 = 5 / 2 ∧
      gaussMetric 2 1 1 1 2 = 11 / 2 := by
  norm_num [gaussMetric, curvatureSq, curvatureInjection, euclideanMetric]

/-- With the same linear stretch but zero injection, the corresponding
Gauss metric remains one through the same depths. -/
theorem stretchTwo_zeroInjection :
    gaussMetric 2 0 1 1 0 = 1 ∧
      gaussMetric 2 0 1 1 1 = 1 ∧
      gaussMetric 2 0 1 1 2 = 1 := by
  norm_num [gaussMetric, curvatureSq, curvatureInjection, euclideanMetric]

#print axioms euclideanMetric_eq_pow_mul
#print axioms euclideanMetric_succ_strictly_increases
#print axioms curvatureSqFixedPoint_is_fixed
#print axioms curvatureSq_sub_fixedPoint_eq
#print axioms curvatureSq_nonneg
#print axioms gaussMetric_succ
#print axioms gaussMetric_succ_strictly_increases
#print axioms gaussMetric_zero_curvatureSource
#print axioms stretchTwo_positiveInjection
#print axioms stretchTwo_zeroInjection

end

end TransientChaosGeometry

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
