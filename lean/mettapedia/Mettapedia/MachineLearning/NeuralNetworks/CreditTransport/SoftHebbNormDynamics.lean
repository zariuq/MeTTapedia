import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# SoftHebb norm dynamics and initialization boundary

Journé et al., *Hebbian Deep Learning Without Feedback* (ICLR 2023,
arXiv:2209.11883), use the local SoftHebb update

`Δw = η y (x - (w · x) w)`

and introduce the norm-dependent rate `η (r - 1)^q`.  The paper motivates the
schedule by the observed convergence of weight vectors toward radius one.

This file derives the exact finite-step squared-norm recurrence.  Its
first-order term points toward the unit sphere only when the signed local gain
`η y (w · x)` is positive.  Negating the update, as in the paper's
anti-Hebbian loser rule, reverses that first-order direction.  At unit norm the
first-order term vanishes, but an ordinary finite Euler step has a nonnegative
quadratic remainder and leaves the sphere whenever the coefficient and
residual are nonzero.  The adaptive rate makes the step exactly zero at radius
one only for positive powers; power zero does not.

The initialization calculation in Appendix A.1.2 also replaces an expected
Euclidean norm by `sqrt(N)` times an expected absolute coordinate.  This is not
an identity for independent coordinates.  An exact two-coordinate Bernoulli
calculation shows that the factorized expression strictly underestimates the
true expected radius.

These results isolate local geometry.  They do not establish Bayesian
optimality, convergence of a stochastic SoftHebb network, or downstream task
efficacy.

Source artifact SHA-256:
`29bfbc60d94cc3833c505f074452bdb727a2c25d5618ef4030a7800d05e258bf`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SoftHebbNormDynamics

open scoped BigOperators Matrix

variable {Coordinate : Type} [Fintype Coordinate]

/-- Squared Euclidean coordinate norm. -/
def normSq (vector : Coordinate → ℝ) : ℝ :=
  vector ⬝ᵥ vector

/-- Total weighted input `u = w · x`. -/
def weightedInput
    (weight input : Coordinate → ℝ) : ℝ :=
  weight ⬝ᵥ input

/-- SoftHebb's local residual `x - u w`. -/
def hebbianResidual
    (weight input : Coordinate → ℝ) : Coordinate → ℝ :=
  input - weightedInput weight input • weight

/-- One SoftHebb-form finite step with the signed coefficient `η y` already
combined. -/
def hebbianStep
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ) : Coordinate → ℝ :=
  weight + coefficient • hebbianResidual weight input

/-- Squared coordinate norm is nonnegative. -/
theorem normSq_nonneg (vector : Coordinate → ℝ) :
    0 ≤ normSq vector := by
  unfold normSq dotProduct
  exact
    Finset.sum_nonneg fun coordinate _ =>
      mul_self_nonneg (vector coordinate)

/-- Squared norm vanishes exactly for the zero vector. -/
theorem normSq_eq_zero_iff (vector : Coordinate → ℝ) :
    normSq vector = 0 ↔ vector = 0 := by
  exact dotProduct_self_eq_zero

/-- The weight/residual overlap is the input drive times the unit-sphere
defect. -/
theorem dot_hebbianResidual
    (weight input : Coordinate → ℝ) :
    weight ⬝ᵥ hebbianResidual weight input =
      weightedInput weight input * (1 - normSq weight) := by
  simp
    [hebbianResidual, weightedInput, normSq, dotProduct_sub,
      dotProduct_smul]
  ring

/-- Generic exact squared-norm expansion for a scaled vector update. -/
theorem normSq_add_scaled
    (weight residual : Coordinate → ℝ)
    (coefficient : ℝ) :
    normSq (weight + coefficient • residual) - normSq weight =
      2 * coefficient * (weight ⬝ᵥ residual) +
        coefficient ^ 2 * normSq residual := by
  simp
    [normSq, add_dotProduct, dotProduct_add, dotProduct_smul,
      smul_dotProduct]
  rw [dotProduct_comm residual weight]
  ring

/-- Exact finite-step SoftHebb squared-norm recurrence. -/
theorem hebbianStep_normSq_change
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ) :
    normSq (hebbianStep coefficient weight input) - normSq weight =
      2 * coefficient * weightedInput weight input *
          (1 - normSq weight) +
        coefficient ^ 2 * normSq (hebbianResidual weight input) := by
  rw [hebbianStep, normSq_add_scaled, dot_hebbianResidual]
  ring

/-- The first-order part of the norm recurrence. -/
def firstOrderNormSqDrift
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ) : ℝ :=
  2 * coefficient * weightedInput weight input *
    (1 - normSq weight)

/-- Positive local gain pushes a sub-unit weight norm outward to first order. -/
theorem firstOrderNormSqDrift_pos_of_below_unit
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ)
    (hgain : 0 < coefficient * weightedInput weight input)
    (hbelow : normSq weight < 1) :
    0 < firstOrderNormSqDrift coefficient weight input := by
  unfold firstOrderNormSqDrift
  nlinarith

/-- Positive local gain pushes a super-unit weight norm inward to first order. -/
theorem firstOrderNormSqDrift_neg_of_above_unit
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ)
    (hgain : 0 < coefficient * weightedInput weight input)
    (habove : 1 < normSq weight) :
    firstOrderNormSqDrift coefficient weight input < 0 := by
  unfold firstOrderNormSqDrift
  nlinarith

/-- Negating the Hebbian coefficient negates the first-order norm drift. -/
theorem firstOrderNormSqDrift_neg_coefficient
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ) :
    firstOrderNormSqDrift (-coefficient) weight input =
      -firstOrderNormSqDrift coefficient weight input := by
  simp [firstOrderNormSqDrift]

/-- Consequently an anti-Hebbian loser step reverses unit-sphere attraction
whenever the corresponding Hebbian sub-unit drift is strict. -/
theorem antiHebbian_firstOrderDrift_neg_of_hebbian_below_unit
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ)
    (hgain : 0 < coefficient * weightedInput weight input)
    (hbelow : normSq weight < 1) :
    firstOrderNormSqDrift (-coefficient) weight input < 0 := by
  rw [firstOrderNormSqDrift_neg_coefficient]
  exact
    neg_neg_of_pos
      (firstOrderNormSqDrift_pos_of_below_unit
        coefficient weight input hgain hbelow)

/-- At unit norm, the entire finite-step change is the nonnegative
second-order residual term. -/
theorem unit_norm_finite_change
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ)
    (hunit : normSq weight = 1) :
    normSq (hebbianStep coefficient weight input) - 1 =
      coefficient ^ 2 * normSq (hebbianResidual weight input) := by
  calc
    normSq (hebbianStep coefficient weight input) - 1 =
        normSq (hebbianStep coefficient weight input) -
          normSq weight := by rw [hunit]
    _ = coefficient ^ 2 * normSq (hebbianResidual weight input) := by
      rw [hebbianStep_normSq_change, hunit]
      ring

/-- Without a zero adaptive coefficient, a nontrivial finite step leaves the
unit sphere even though its first-order drift vanishes. -/
theorem unit_norm_nontrivial_step_leaves_sphere
    (coefficient : ℝ)
    (weight input : Coordinate → ℝ)
    (hunit : normSq weight = 1)
    (hcoefficient : coefficient ≠ 0)
    (hresidual : hebbianResidual weight input ≠ 0) :
    1 < normSq (hebbianStep coefficient weight input) := by
  have hresidualSq :
      0 < normSq (hebbianResidual weight input) := by
    have hnonneg := normSq_nonneg (hebbianResidual weight input)
    have hne :
        normSq (hebbianResidual weight input) ≠ 0 := by
      exact (normSq_eq_zero_iff _).not.mpr hresidual
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hcoefficientSq : 0 < coefficient ^ 2 :=
    sq_pos_of_ne_zero hcoefficient
  have hchange :=
    unit_norm_finite_change coefficient weight input hunit
  have hproduct :
      0 < coefficient ^ 2 *
        normSq (hebbianResidual weight input) :=
    mul_pos hcoefficientSq hresidualSq
  nlinarith

/-! ## Norm-dependent adaptive-rate boundary -/

/-- The paper's norm-dependent rate for a natural power. -/
def adaptiveRate
    (base radius : ℝ) (power : ℕ) : ℝ :=
  base * (radius - 1) ^ power

/-- Every positive natural power makes the adaptive rate exactly zero at unit
radius. -/
@[simp] theorem adaptiveRate_unit_successor
    (base : ℝ) (power : ℕ) :
    adaptiveRate base 1 (power + 1) = 0 := by
  simp [adaptiveRate]

/-- Power zero does not stabilize at unit radius. -/
@[simp] theorem adaptiveRate_unit_zero
    (base : ℝ) :
    adaptiveRate base 1 0 = base := by
  simp [adaptiveRate]

/-- With power one and positive base rate, radii below one produce a negative
learning rate. -/
theorem adaptiveRate_power_one_neg_below_unit
    (base radius : ℝ)
    (hbase : 0 < base)
    (hradius : radius < 1) :
    adaptiveRate base radius 1 < 0 := by
  simp [adaptiveRate]
  nlinarith

/-- An even power avoids that sign reversal. -/
theorem adaptiveRate_power_two_nonneg
    (base radius : ℝ)
    (hbase : 0 ≤ base) :
    0 ≤ adaptiveRate base radius 2 := by
  simp [adaptiveRate]
  positivity

/-! ## Appendix A.1.2 expectation counterexample -/

/-- Euclidean radius of a two-coordinate vector. -/
noncomputable def radiusTwo (first second : ℝ) : ℝ :=
  Real.sqrt (first ^ 2 + second ^ 2)

/-- Exact expected radius of two independent Bernoulli `{0,1}` coordinates. -/
noncomputable def bernoulliPairExpectedRadius : ℝ :=
  (radiusTwo 0 0 + radiusTwo 0 1 +
    radiusTwo 1 0 + radiusTwo 1 1) / 4

/-- The factorized `sqrt(N) E|w|` expression used in the source calculation. -/
noncomputable def bernoulliPairFactorizedRadius : ℝ :=
  Real.sqrt 2 / 2

/-- The exact four-outcome expectation. -/
theorem bernoulliPairExpectedRadius_formula :
    bernoulliPairExpectedRadius =
      (2 + Real.sqrt 2) / 4 := by
  norm_num [bernoulliPairExpectedRadius, radiusTwo]

/-- `sqrt 2` is strictly below two. -/
theorem sqrt_two_lt_two :
    Real.sqrt 2 < 2 :=
  (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by norm_num)

/-- The factorized expression strictly underestimates the true expected
Euclidean radius for independent Bernoulli coordinates. -/
theorem bernoulliPair_factorizedRadius_lt_expected :
    bernoulliPairFactorizedRadius <
      bernoulliPairExpectedRadius := by
  rw [bernoulliPairExpectedRadius_formula]
  unfold bernoulliPairFactorizedRadius
  linarith [sqrt_two_lt_two]

end SoftHebbNormDynamics

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
