import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DeepLineRestriction

/-!
# Deep-linear singular-mode dynamics

Saxe, McClelland, and Ganguli, *Exact solutions to the nonlinear dynamics of
learning in deep linear neural networks* (2013), reduce gradient flow on an
orthogonally decoupled singular mode to scalar factor dynamics.  The source
PDF has SHA-256
`f187bedbefaafad246c040d0384f1ca3da222c1f21e8ca9e264cadf5d64f8a12`.

This file recovers source Equations (8)--(15) and strengthens their algebraic
core to an arbitrary finite number of scalar factors.  Coordinate
perturbation has an exact quadratic energy law.  The product derivative under
gradient flow has the sign of the remaining target error, every pairwise
squared-factor imbalance has zero instantaneous rate, and a genuine
two-factor trajectory conserves that imbalance for all real times.

On the balanced two-factor manifold, the product obeys the logistic equation
from source Equation (10).  The source's closed form is proved to satisfy
that equation, start at the declared initial value, remain strictly between
initial and target, and rise strictly monotonically.  Exact zero
initialization is a dead fixed point for the two-factor model, whereas a
one-factor model remains live.  Finally, a large explicit Euler step raises
the loss, separating continuous gradient-flow theory from unrestricted
finite-step training.

The mode-decoupling and whitened-input hypotheses remain load-bearing.  No
theorem below claims that arbitrary random nonlinear networks remain on the
decoupled manifold or that the source's empirical learning curves follow
from these scalar identities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

namespace DeepLinearModeDynamics

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Arbitrary finite factor chains -/

/-- End-to-end strength of one scalar singular mode. -/
def factorProduct {depth : ℕ} (factor : Fin depth → ℝ) : ℝ :=
  ∏ index, factor index

/-- Product of all mode factors except one coordinate. -/
def productExcept {depth : ℕ}
    (factor : Fin depth → ℝ) (index : Fin depth) : ℝ :=
  ∏ other ∈ Finset.univ.erase index, factor other

/-- Squared prediction error for one decoupled singular mode. -/
def modeEnergy {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ) : ℝ :=
  (target - factorProduct factor) ^ 2 / 2

/-- Negative coordinate gradient of `modeEnergy`. -/
def factorFlow {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ) (index : Fin depth) : ℝ :=
  productExcept factor index * (target - factorProduct factor)

/-- Perturb one scalar factor. -/
def perturbFactor {depth : ℕ}
    (factor : Fin depth → ℝ) (index : Fin depth) (delta : ℝ) :
    Fin depth → ℝ :=
  fun current =>
    if current = index then factor current + delta else factor current

/-- Restoring the omitted coordinate recovers the complete factor product. -/
theorem factor_mul_productExcept {depth : ℕ}
    (factor : Fin depth → ℝ) (index : Fin depth) :
    factor index * productExcept factor index = factorProduct factor := by
  simp [factorProduct, productExcept, Finset.mul_prod_erase]

/-- Exact product response to one coordinate perturbation. -/
theorem factorProduct_perturbFactor_exact {depth : ℕ}
    (factor : Fin depth → ℝ) (index : Fin depth) (delta : ℝ) :
    factorProduct (perturbFactor factor index delta) =
      factorProduct factor + delta * productExcept factor index := by
  classical
  have productErase :
      (∏ other ∈ Finset.univ.erase index,
          perturbFactor factor index delta other) =
        productExcept factor index := by
    unfold productExcept
    apply Finset.prod_congr rfl
    intro other otherMem
    have otherNeIndex : other ≠ index :=
      Finset.ne_of_mem_erase otherMem
    simp [perturbFactor, otherNeIndex]
  rw [show factorProduct (perturbFactor factor index delta) =
      perturbFactor factor index delta index *
        ∏ other ∈ Finset.univ.erase index,
          perturbFactor factor index delta other by
    simp [factorProduct, Finset.mul_prod_erase]]
  rw [productErase]
  simp [perturbFactor]
  rw [show factorProduct factor =
      factor index * productExcept factor index by
    exact (factor_mul_productExcept factor index).symm]
  ring

/-- Exact coordinate energy law.  Its linear coefficient is the negative of
`factorFlow`, and its coordinate curvature is the squared omitted product. -/
theorem modeEnergy_perturbFactor_exact {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ)
    (index : Fin depth) (delta : ℝ) :
    modeEnergy target (perturbFactor factor index delta) =
      modeEnergy target factor -
        delta * factorFlow target factor index +
          delta ^ 2 / 2 * productExcept factor index ^ 2 := by
  rw [modeEnergy, modeEnergy, factorProduct_perturbFactor_exact]
  simp only [factorFlow]
  ring

/-- Directional derivative of the factor product. -/
def productDirectionalDerivative {depth : ℕ}
    (factor velocity : Fin depth → ℝ) : ℝ :=
  ∑ index, velocity index * productExcept factor index

/-- Source Equation (15), generalized off the balanced manifold: under
gradient flow the product moves by target error times a sum of squares. -/
theorem factorFlow_productDerivative_exact {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ) :
    productDirectionalDerivative factor (factorFlow target factor) =
      (target - factorProduct factor) *
        ∑ index, productExcept factor index ^ 2 := by
  unfold productDirectionalDerivative factorFlow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Directional rate of the mode energy. -/
def modeEnergyDirectionalRate {depth : ℕ}
    (target : ℝ) (factor velocity : Fin depth → ℝ) : ℝ :=
  -(target - factorProduct factor) *
    productDirectionalDerivative factor velocity

/-- Gradient flow dissipates mode energy by an exact sum-of-squares law. -/
theorem modeEnergyDirectionalRate_factorFlow_exact {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ) :
    modeEnergyDirectionalRate target factor (factorFlow target factor) =
      -(target - factorProduct factor) ^ 2 *
        ∑ index, productExcept factor index ^ 2 := by
  rw [modeEnergyDirectionalRate, factorFlow_productDerivative_exact]
  ring

/-- The exact flow energy rate is always nonpositive. -/
theorem modeEnergyDirectionalRate_factorFlow_nonpositive {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ) :
    modeEnergyDirectionalRate target factor (factorFlow target factor) ≤ 0 := by
  rw [modeEnergyDirectionalRate_factorFlow_exact]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _))
    (Finset.sum_nonneg fun index _ =>
      sq_nonneg (productExcept factor index))

/-- The flow rate is strictly negative away from the target whenever at
least one coordinate has a nonzero complementary product. -/
theorem modeEnergyDirectionalRate_factorFlow_negative {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ)
    (targetMismatch : target ≠ factorProduct factor)
    (liveCoordinate :
      ∃ index, productExcept factor index ≠ 0) :
    modeEnergyDirectionalRate target factor (factorFlow target factor) < 0 := by
  rw [modeEnergyDirectionalRate_factorFlow_exact]
  obtain ⟨index, indexLive⟩ := liveCoordinate
  have sumPositive :
      0 < ∑ current, productExcept factor current ^ 2 := by
    have oneTermLe :
        productExcept factor index ^ 2 ≤
          ∑ current, productExcept factor current ^ 2 := by
      exact Finset.single_le_sum
        (fun current _ => sq_nonneg (productExcept factor current))
        (Finset.mem_univ index)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero indexLive) oneTermLe
  have mismatchPositive :
      0 < (target - factorProduct factor) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr targetMismatch)
  nlinarith

/-- The source's pairwise squared-factor conservation law, generalized to
every finite factor chain at the vector-field level. -/
theorem pairwiseSquareImbalance_instantaneous_zero {depth : ℕ}
    (target : ℝ) (factor : Fin depth → ℝ)
    (first second : Fin depth) :
    2 * factor first * factorFlow target factor first -
        2 * factor second * factorFlow target factor second =
      0 := by
  rw [factorFlow, factorFlow]
  calc
    2 * factor first *
          (productExcept factor first *
            (target - factorProduct factor)) -
        2 * factor second *
          (productExcept factor second *
            (target - factorProduct factor)) =
      2 * (factor first * productExcept factor first) *
          (target - factorProduct factor) -
        2 * (factor second * productExcept factor second) *
          (target - factorProduct factor) := by
            ring
    _ = 0 := by
      rw [factor_mul_productExcept, factor_mul_productExcept]
      ring

/-! ## Two-factor source dynamics and conservation -/

/-- Two scalar factors as a finite factor chain. -/
def twoFactor (left right : ℝ) : Fin 2 → ℝ :=
  ![left, right]

theorem factorProduct_twoFactor
    (left right : ℝ) :
    factorProduct (twoFactor left right) = left * right := by
  simp [factorProduct, twoFactor, Fin.prod_univ_two]

theorem productExcept_twoFactor_zero
    (left right : ℝ) :
    productExcept (twoFactor left right) 0 = right := by
  rw [productExcept, Finset.univ_fin2]
  norm_num [twoFactor]

theorem productExcept_twoFactor_one
    (left right : ℝ) :
    productExcept (twoFactor left right) 1 = left := by
  rw [productExcept, Finset.univ_fin2]
  have eraseOne :
      ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by
    decide
  rw [eraseOne]
  simp [twoFactor]

/-- Source Equation (8), first factor. -/
theorem factorFlow_twoFactor_zero
    (target left right : ℝ) :
    factorFlow target (twoFactor left right) 0 =
      right * (target - left * right) := by
  rw [factorFlow, factorProduct_twoFactor, productExcept_twoFactor_zero]

/-- Source Equation (8), second factor. -/
theorem factorFlow_twoFactor_one
    (target left right : ℝ) :
    factorFlow target (twoFactor left right) 1 =
      left * (target - left * right) := by
  rw [factorFlow, factorProduct_twoFactor, productExcept_twoFactor_one]

/-- A differentiable trajectory satisfying the two-factor source ODE. -/
structure TwoFactorTrajectory (target : ℝ) where
  left : ℝ → ℝ
  right : ℝ → ℝ
  left_hasDerivAt :
    ∀ time,
      HasDerivAt left
        (right time * (target - left time * right time)) time
  right_hasDerivAt :
    ∀ time,
      HasDerivAt right
        (left time * (target - left time * right time)) time

/-- Pairwise squared-factor imbalance along a trajectory. -/
def squareImbalance {target : ℝ}
    (trajectory : TwoFactorTrajectory target) (time : ℝ) : ℝ :=
  trajectory.left time ^ 2 - trajectory.right time ^ 2

/-- The imbalance has zero derivative at every time. -/
theorem squareImbalance_hasDerivAt_zero {target : ℝ}
    (trajectory : TwoFactorTrajectory target) (time : ℝ) :
    HasDerivAt (squareImbalance trajectory) 0 time := by
  have leftSquare :=
    (trajectory.left_hasDerivAt time).mul
      (trajectory.left_hasDerivAt time)
  have rightSquare :=
    (trajectory.right_hasDerivAt time).mul
      (trajectory.right_hasDerivAt time)
  have difference := leftSquare.sub rightSquare
  have pathEquality :
      squareImbalance trajectory =ᶠ[𝓝 time]
        (trajectory.left * trajectory.left -
          trajectory.right * trajectory.right) :=
    Eventually.of_forall fun current => by
      simp [squareImbalance, pow_two]
  exact
    (difference.congr_of_eventuallyEq pathEquality).congr_deriv (by ring)

/-- Source conservation law: squared-factor imbalance is constant along every
genuine two-factor trajectory. -/
theorem squareImbalance_conserved {target : ℝ}
    (trajectory : TwoFactorTrajectory target) (time : ℝ) :
    squareImbalance trajectory time =
      squareImbalance trajectory 0 := by
  by_cases timeNonnegative : 0 ≤ time
  · exact constant_of_has_deriv_right_zero (a := 0) (b := time)
      (fun current _ =>
        ((squareImbalance_hasDerivAt_zero trajectory current).continuousAt).continuousWithinAt)
      (fun current _ =>
        (squareImbalance_hasDerivAt_zero trajectory current).hasDerivWithinAt)
      time ⟨timeNonnegative, le_rfl⟩
  · have timeNonpositive : time ≤ 0 :=
      le_of_not_ge timeNonnegative
    have conservationFromTime :=
      constant_of_has_deriv_right_zero (a := time) (b := 0)
        (fun current _ =>
          ((squareImbalance_hasDerivAt_zero trajectory current).continuousAt).continuousWithinAt)
        (fun current _ =>
          (squareImbalance_hasDerivAt_zero trajectory current).hasDerivWithinAt)
        0 ⟨timeNonpositive, le_rfl⟩
    exact conservationFromTime.symm

/-! ## Balanced logistic mode -/

/-- Source Equation (12), written without division by the initial mode
strength. -/
def balancedProductPath
    (target initial time : ℝ) : ℝ :=
  target * initial * Real.exp (2 * target * time) /
    (initial * Real.exp (2 * target * time) + (target - initial))

private theorem quotientDerivativeIdentity
    (target initial exponential : ℝ)
    (denominatorNonzero :
      initial * exponential + (target - initial) ≠ 0) :
    ((target * initial * (exponential * (2 * target)) *
          (initial * exponential + (target - initial)) -
        target * initial * exponential *
          (initial * (exponential * (2 * target)))) /
      (initial * exponential + (target - initial)) ^ 2) =
      2 *
        (target * initial * exponential /
          (initial * exponential + (target - initial))) *
        (target -
          target * initial * exponential /
            (initial * exponential + (target - initial))) := by
  field_simp [denominatorNonzero]

/-- The closed form satisfies the balanced product ODE from source Equation
(10). -/
theorem balancedProductPath_hasDerivAt
    (target initial time : ℝ)
    (initialPositive : 0 < initial)
    (initialBelowTarget : initial < target) :
    HasDerivAt (balancedProductPath target initial)
      (2 * balancedProductPath target initial time *
        (target - balancedProductPath target initial time)) time := by
  have innerDerivative :
      HasDerivAt (fun current : ℝ => 2 * target * current)
        (2 * target) time := by
    have rawDerivative :=
      (hasDerivAt_id time).const_mul (2 * target)
    have pathEquality :
        (fun current : ℝ => 2 * target * current) =ᶠ[𝓝 time]
          (fun current : ℝ => (2 * target) * id current) :=
      Eventually.of_forall fun _ => rfl
    exact
      (rawDerivative.congr_of_eventuallyEq pathEquality).congr_deriv
        (by ring)
  have exponentialDerivative :
      HasDerivAt
        (fun current : ℝ => Real.exp (2 * target * current))
        (Real.exp (2 * target * time) * (2 * target)) time := by
    have composition :=
      (Real.hasDerivAt_exp (2 * target * time)).comp time innerDerivative
    have pathEquality :
        (fun current : ℝ => Real.exp (2 * target * current)) =ᶠ[𝓝 time]
          (Real.exp ∘ fun current : ℝ => 2 * target * current) :=
      Eventually.of_forall fun _ => rfl
    exact composition.congr_of_eventuallyEq pathEquality
  have denominatorPositive :
      0 <
        initial * Real.exp (2 * target * time) +
          (target - initial) := by
    have exponentialPositive :
        0 < Real.exp (2 * target * time) :=
      Real.exp_pos _
    nlinarith
  have numeratorDerivative :=
    exponentialDerivative.const_mul (target * initial)
  have denominatorDerivative :=
    (exponentialDerivative.const_mul initial).add_const
      (target - initial)
  have quotientDerivative :=
    numeratorDerivative.div denominatorDerivative
      (ne_of_gt denominatorPositive)
  have pathEquality :
      balancedProductPath target initial =ᶠ[𝓝 time]
        ((fun current : ℝ =>
          target * initial * Real.exp (2 * target * current)) /
        fun current : ℝ =>
          initial * Real.exp (2 * target * current) +
            (target - initial)) :=
    Eventually.of_forall fun _ => rfl
  apply
    (quotientDerivative.congr_of_eventuallyEq pathEquality.symm).congr_deriv
  simpa only [balancedProductPath] using
    quotientDerivativeIdentity target initial
      (Real.exp (2 * target * time))
      (ne_of_gt denominatorPositive)

/-- The closed form starts at the declared initial product. -/
theorem balancedProductPath_zero
    (target initial : ℝ) (targetNonzero : target ≠ 0) :
    balancedProductPath target initial 0 = initial := by
  simp [balancedProductPath]
  field_simp [targetNonzero]

/-- Positive subtarget initialization keeps the logistic path strictly inside
the positive target interval at every finite time. -/
theorem balancedProductPath_mem_Ioo
    (target initial time : ℝ)
    (initialPositive : 0 < initial)
    (initialBelowTarget : initial < target) :
    balancedProductPath target initial time ∈ Set.Ioo 0 target := by
  have targetPositive : 0 < target :=
    lt_trans initialPositive initialBelowTarget
  have exponentialPositive :
      0 < Real.exp (2 * target * time) :=
    Real.exp_pos _
  have denominatorPositive :
      0 <
        initial * Real.exp (2 * target * time) +
          (target - initial) := by
    nlinarith
  constructor
  · exact div_pos
      (mul_pos (mul_pos targetPositive initialPositive)
        exponentialPositive)
      denominatorPositive
  · rw [balancedProductPath, div_lt_iff₀ denominatorPositive]
    nlinarith

/-- The exact source learning curve is strictly increasing. -/
theorem balancedProductPath_strictMono
    (target initial : ℝ)
    (initialPositive : 0 < initial)
    (initialBelowTarget : initial < target) :
    StrictMono (balancedProductPath target initial) := by
  apply strictMono_of_hasDerivAt_pos
  · intro time
    exact balancedProductPath_hasDerivAt target initial time
      initialPositive initialBelowTarget
  · intro time
    have pathBounds :=
      balancedProductPath_mem_Ioo target initial time
        initialPositive initialBelowTarget
    exact mul_pos
      (mul_pos (by norm_num) pathBounds.1)
      (sub_pos.mpr pathBounds.2)

/-- Algebraic target-gap identity for the logistic quotient. -/
private theorem targetGapIdentity
    (target initial exponential : ℝ)
    (denominatorNonzero :
      initial * exponential + (target - initial) ≠ 0) :
    target -
        target * initial * exponential /
          (initial * exponential + (target - initial)) =
      target * (target - initial) /
        (initial * exponential + (target - initial)) := by
  field_simp [denominatorNonzero]
  ring

/-- Exact remaining target gap along the logistic path. -/
theorem target_sub_balancedProductPath
    (target initial time : ℝ)
    (initialPositive : 0 < initial)
    (initialBelowTarget : initial < target) :
    target - balancedProductPath target initial time =
      target * (target - initial) /
        (initial * Real.exp (2 * target * time) +
          (target - initial)) := by
  have exponentialPositive :
      0 < Real.exp (2 * target * time) :=
    Real.exp_pos _
  have denominatorPositive :
      0 <
        initial * Real.exp (2 * target * time) +
          (target - initial) := by
    nlinarith
  simpa only [balancedProductPath] using
    targetGapIdentity target initial (Real.exp (2 * target * time))
      (ne_of_gt denominatorPositive)

/-! ## Initialization and discretization boundaries -/

/-- Exact zero initialization is a dead two-factor fixed point. -/
theorem twoFactor_origin_flow_zero
    (target : ℝ) :
    factorFlow target (twoFactor 0 0) = 0 := by
  funext index
  fin_cases index
  · simpa using factorFlow_twoFactor_zero target 0 0
  · simpa using factorFlow_twoFactor_one target 0 0

/-- The analogous one-factor model remains live at the origin. -/
theorem oneFactor_origin_flow_live
    (target : ℝ) :
    factorFlow target (fun _ : Fin 1 => 0) 0 = target := by
  simp [factorFlow, productExcept, factorProduct]

/-- An arbitrarily simple positive balanced seed escapes the dead origin. -/
theorem positive_balanced_seed_is_live :
    factorFlow 1 (twoFactor (1 / 2) (1 / 2)) 0 = (3 / 8 : ℝ) ∧
      factorFlow 1 (twoFactor (1 / 2) (1 / 2)) 1 = (3 / 8 : ℝ) := by
  constructor
  · rw [factorFlow_twoFactor_zero]
    norm_num
  · rw [factorFlow_twoFactor_one]
    norm_num

/-- One simultaneous explicit-Euler update of source Equation (8). -/
def twoFactorEulerStep
    (rate target left right : ℝ) : ℝ × ℝ :=
  (left + rate * right * (target - left * right),
    right + rate * left * (target - left * right))

/-- Two-factor specialization of the mode energy. -/
def twoFactorEnergy
    (target left right : ℝ) : ℝ :=
  (target - left * right) ^ 2 / 2

/-- Continuous energy dissipation does not license an unrestricted Euler
rate: a large finite step can increase the source energy. -/
theorem largeEulerStep_raises_energy :
    let next :=
      twoFactorEulerStep 10 1 (1 / 2 : ℝ) (1 / 2 : ℝ)
    twoFactorEnergy 1 next.1 next.2 >
      twoFactorEnergy 1 (1 / 2) (1 / 2) := by
  norm_num [twoFactorEulerStep, twoFactorEnergy]

#print axioms factorProduct_perturbFactor_exact
#print axioms modeEnergy_perturbFactor_exact
#print axioms factorFlow_productDerivative_exact
#print axioms modeEnergyDirectionalRate_factorFlow_negative
#print axioms pairwiseSquareImbalance_instantaneous_zero
#print axioms squareImbalance_conserved
#print axioms balancedProductPath_hasDerivAt
#print axioms balancedProductPath_strictMono
#print axioms twoFactor_origin_flow_zero
#print axioms largeEulerStep_raises_energy

end

end DeepLinearModeDynamics

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
