import Mathlib.Tactic

/-!
# Regularized residual mixing

Scieur, Oyallon, d'Aspremont, and Bach,
*Online Regularized Nonlinear Acceleration*,
arXiv:1805.09639, Algorithm 1 and Proposition 2.2, regularize the
least-squares residual-mixing problem by the squared norm of its affine
coefficients.  The authenticated primary PDF has SHA-256
`105d81e14eeaa31c2e1888666412fec82214dcf5506bbe45e223dd2f9cff3194`.

This file isolates the proof mechanism behind the source bound.  Comparing a
regularized minimizer with uniform averaging bounds the squared coefficient
norm by `(1 + 1 / regularization) / history`.  The result is stated for any
nonnegative residual energy with a certified uniform-average scale, so it
applies beyond matrix residuals.

For two scalar residuals we also construct the actual affine solver, prove its
global optimality by an exact completed-square identity, and instantiate the
coefficient bound.  A matching negative fixture shows that without positive
regularization, residual minimization can permit affine coefficients of
arbitrarily large norm.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RegularizedResidualMixing

open Finset

noncomputable section

/-! ## Generic coefficient-energy bound -/

/-- Squared Euclidean norm of a finite coefficient vector. -/
def coefficientEnergy {history : ℕ} (coefficient : Fin history → ℝ) : ℝ :=
  ∑ index, coefficient index ^ 2

/-- Uniform affine coefficients over a nonempty history. -/
def uniformCoefficient (history : ℕ) : Fin history → ℝ :=
  fun _ => 1 / (history : ℝ)

/-- Residual energy plus the source's scale-normalized coefficient penalty. -/
def regularizedResidualObjective {history : ℕ}
    (residualEnergy : (Fin history → ℝ) → ℝ)
    (residualScale regularization : ℝ)
    (coefficient : Fin history → ℝ) : ℝ :=
  residualEnergy coefficient +
    regularization * residualScale * coefficientEnergy coefficient

theorem coefficientEnergy_nonneg {history : ℕ}
    (coefficient : Fin history → ℝ) :
    0 ≤ coefficientEnergy coefficient := by
  exact Finset.sum_nonneg fun index _ => sq_nonneg (coefficient index)

theorem uniformCoefficient_sum
    {history : ℕ} (history_pos : 0 < history) :
    ∑ index, uniformCoefficient history index = 1 := by
  simp [uniformCoefficient, history_pos.ne']

theorem uniformCoefficient_energy
    {history : ℕ} (history_pos : 0 < history) :
    coefficientEnergy (uniformCoefficient history) =
      1 / (history : ℝ) := by
  have history_cast_ne : (history : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr history_pos.ne'
  simp only [coefficientEnergy, uniformCoefficient, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Abstract form of Proposition 2.2.

The only matrix-specific input needed by the proof is that the residual
energy of uniform averaging is at most `residualScale / history`.  This is
the standard operator/Frobenius norm estimate for the source's residual
matrix. -/
theorem coefficientEnergy_le_of_regularized_minimizes
    {history : ℕ} (history_pos : 0 < history)
    (residualEnergy : (Fin history → ℝ) → ℝ)
    (residualScale regularization : ℝ)
    (coefficient : Fin history → ℝ)
    (regularization_pos : 0 < regularization)
    (residualScale_pos : 0 < residualScale)
    (residualEnergy_nonneg : 0 ≤ residualEnergy coefficient)
    (uniformResidual_le :
      residualEnergy (uniformCoefficient history) ≤
        residualScale / (history : ℝ))
    (minimizesUniform :
      regularizedResidualObjective residualEnergy residualScale
          regularization coefficient ≤
        regularizedResidualObjective residualEnergy residualScale
          regularization (uniformCoefficient history)) :
    coefficientEnergy coefficient ≤
      (1 + 1 / regularization) / (history : ℝ) := by
  have history_cast_pos : 0 < (history : ℝ) := by exact_mod_cast history_pos
  have penalty_pos : 0 < regularization * residualScale :=
    mul_pos regularization_pos residualScale_pos
  have lower :
      regularization * residualScale * coefficientEnergy coefficient ≤
        regularizedResidualObjective residualEnergy residualScale
          regularization coefficient := by
    simp only [regularizedResidualObjective]
    linarith
  have upper :
      regularizedResidualObjective residualEnergy residualScale
          regularization (uniformCoefficient history) ≤
        residualScale / (history : ℝ) +
          regularization * residualScale / (history : ℝ) := by
    rw [regularizedResidualObjective,
      uniformCoefficient_energy history_pos]
    calc
      residualEnergy (uniformCoefficient history) +
          regularization * residualScale * (1 / (history : ℝ)) ≤
        residualScale / (history : ℝ) +
          regularization * residualScale * (1 / (history : ℝ)) :=
            by
              simpa [add_comm] using
                add_le_add_right uniformResidual_le
                  (regularization * residualScale * (1 / (history : ℝ)))
      _ = residualScale / (history : ℝ) +
          regularization * residualScale / (history : ℝ) := by ring
  have combined :
      regularization * residualScale * coefficientEnergy coefficient ≤
        residualScale / (history : ℝ) +
          regularization * residualScale / (history : ℝ) :=
    lower.trans (minimizesUniform.trans upper)
  refine le_of_mul_le_mul_right ?_ penalty_pos
  calc
    coefficientEnergy coefficient * (regularization * residualScale)
        = regularization * residualScale * coefficientEnergy coefficient := by
            ring
    _ ≤ residualScale / (history : ℝ) +
          regularization * residualScale / (history : ℝ) := combined
    _ = ((1 + 1 / regularization) / (history : ℝ)) *
          (regularization * residualScale) := by
            field_simp
            ring

/-! ## The actual two-history scalar solver -/

/-- Affine two-history coefficient vector parameterized by its first entry. -/
def twoHistoryCoefficient (first : ℝ) : Fin 2 → ℝ
  | 0 => first
  | 1 => 1 - first

@[simp] theorem twoHistoryCoefficient_zero (first : ℝ) :
    twoHistoryCoefficient first 0 = first := rfl

@[simp] theorem twoHistoryCoefficient_one (first : ℝ) :
    twoHistoryCoefficient first 1 = 1 - first := rfl

theorem twoHistoryCoefficient_sum (first : ℝ) :
    ∑ index, twoHistoryCoefficient first index = 1 := by
  simp [Fin.sum_univ_two]

theorem twoHistoryCoefficient_energy (first : ℝ) :
    coefficientEnergy (twoHistoryCoefficient first) =
      first ^ 2 + (1 - first) ^ 2 := by
  simp [coefficientEnergy, Fin.sum_univ_two]

/-- Squared residual of an affine mixture of two scalar residuals. -/
def twoHistoryResidualEnergy
    (firstResidual secondResidual : ℝ)
    (coefficient : Fin 2 → ℝ) : ℝ :=
  (firstResidual * coefficient 0 +
    secondResidual * coefficient 1) ^ 2

theorem twoHistoryResidualEnergy_nonneg
    (firstResidual secondResidual : ℝ)
    (coefficient : Fin 2 → ℝ) :
    0 ≤ twoHistoryResidualEnergy
      firstResidual secondResidual coefficient :=
  sq_nonneg _

/-- Closed-form first coefficient for the regularized two-history problem.
The `residualScale` parameter is the certified matrix-residual scale used by
the source normalization. -/
def twoHistoryRegularizedFirst
    (firstResidual secondResidual residualScale regularization : ℝ) : ℝ :=
  let difference := firstResidual - secondResidual
  let penalty := regularization * residualScale
  (penalty - difference * secondResidual) /
    (difference ^ 2 + 2 * penalty)

/-- The scalar quadratic whose minimizer supplies the two-history RNA
coefficient. -/
def scalarAffineMixObjective
    (difference base penalty candidate : ℝ) : ℝ :=
  (difference * candidate + base) ^ 2 +
    penalty * (candidate ^ 2 + (1 - candidate) ^ 2)

/-- Closed-form minimizer of `scalarAffineMixObjective` when its quadratic
coefficient is nonzero. -/
def scalarAffineMixMinimizer
    (difference base penalty : ℝ) : ℝ :=
  (penalty - difference * base) / (difference ^ 2 + 2 * penalty)

/-- Completed-square identity underlying the explicit solver. -/
theorem scalarAffineMixObjective_sub_of_stationary
    (difference base penalty candidate minimizer : ℝ)
    (stationary :
      (difference ^ 2 + 2 * penalty) * minimizer =
        penalty - difference * base) :
    scalarAffineMixObjective difference base penalty candidate -
      scalarAffineMixObjective difference base penalty minimizer =
      (difference ^ 2 + 2 * penalty) *
        (candidate - minimizer) ^ 2 := by
  have factorization :
      scalarAffineMixObjective difference base penalty candidate -
          scalarAffineMixObjective difference base penalty minimizer -
            (difference ^ 2 + 2 * penalty) *
              (candidate - minimizer) ^ 2 =
        2 * (candidate - minimizer) *
          ((difference ^ 2 + 2 * penalty) * minimizer +
            difference * base - penalty) := by
    simp only [scalarAffineMixObjective]
    ring
  have stationary_zero :
      2 * (candidate - minimizer) *
          ((difference ^ 2 + 2 * penalty) * minimizer +
            difference * base - penalty) = 0 := by
    rw [stationary]
    ring
  linarith

theorem scalarAffineMixMinimizer_stationary
    (difference base penalty : ℝ)
    (denominator_ne : difference ^ 2 + 2 * penalty ≠ 0) :
    (difference ^ 2 + 2 * penalty) *
        scalarAffineMixMinimizer difference base penalty =
      penalty - difference * base := by
  unfold scalarAffineMixMinimizer
  exact mul_div_cancel₀ _ denominator_ne

theorem scalarAffineMixObjective_sub_at_minimizer
    (difference base penalty candidate : ℝ)
    (denominator_ne : difference ^ 2 + 2 * penalty ≠ 0) :
    scalarAffineMixObjective difference base penalty candidate -
      scalarAffineMixObjective difference base penalty
        (scalarAffineMixMinimizer difference base penalty) =
      (difference ^ 2 + 2 * penalty) *
        (candidate -
          scalarAffineMixMinimizer difference base penalty) ^ 2 :=
  scalarAffineMixObjective_sub_of_stationary
    difference base penalty candidate
    (scalarAffineMixMinimizer difference base penalty)
    (scalarAffineMixMinimizer_stationary
      difference base penalty denominator_ne)

theorem regularizedTwoHistoryObjective_eq_scalarAffine
    (firstResidual secondResidual residualScale regularization candidate : ℝ) :
    regularizedResidualObjective
        (twoHistoryResidualEnergy firstResidual secondResidual)
        residualScale regularization
        (twoHistoryCoefficient candidate) =
      scalarAffineMixObjective
        (firstResidual - secondResidual) secondResidual
        (regularization * residualScale) candidate := by
  simp [regularizedResidualObjective, twoHistoryResidualEnergy,
    twoHistoryCoefficient_energy, scalarAffineMixObjective]
  ring

@[simp] theorem twoHistoryRegularizedFirst_eq_scalarAffineMinimizer
    (firstResidual secondResidual residualScale regularization : ℝ) :
    twoHistoryRegularizedFirst firstResidual secondResidual
        residualScale regularization =
      scalarAffineMixMinimizer
        (firstResidual - secondResidual) secondResidual
        (regularization * residualScale) := by
  rfl

/-- Exact completed-square identity for the two-history objective. -/
theorem twoHistory_objective_sub_at_solver
    (firstResidual secondResidual residualScale regularization candidate : ℝ)
    (denominator_ne :
      (firstResidual - secondResidual) ^ 2 +
          2 * (regularization * residualScale) ≠ 0) :
    regularizedResidualObjective
        (twoHistoryResidualEnergy firstResidual secondResidual)
        residualScale regularization
        (twoHistoryCoefficient candidate) -
      regularizedResidualObjective
        (twoHistoryResidualEnergy firstResidual secondResidual)
        residualScale regularization
        (twoHistoryCoefficient
          (twoHistoryRegularizedFirst firstResidual secondResidual
            residualScale regularization)) =
      ((firstResidual - secondResidual) ^ 2 +
          2 * (regularization * residualScale)) *
        (candidate -
          twoHistoryRegularizedFirst firstResidual secondResidual
            residualScale regularization) ^ 2 := by
  rw [regularizedTwoHistoryObjective_eq_scalarAffine,
    regularizedTwoHistoryObjective_eq_scalarAffine,
    twoHistoryRegularizedFirst_eq_scalarAffineMinimizer]
  exact scalarAffineMixObjective_sub_at_minimizer
    (firstResidual - secondResidual) secondResidual
      (regularization * residualScale) candidate denominator_ne

/-- Positive regularization and scale make the explicit two-history solver a
global minimizer among all affine two-history mixtures. -/
theorem twoHistoryRegularizedFirst_minimizes
    (firstResidual secondResidual residualScale regularization candidate : ℝ)
    (residualScale_pos : 0 < residualScale)
    (regularization_pos : 0 < regularization) :
    regularizedResidualObjective
        (twoHistoryResidualEnergy firstResidual secondResidual)
        residualScale regularization
        (twoHistoryCoefficient
          (twoHistoryRegularizedFirst firstResidual secondResidual
            residualScale regularization)) ≤
      regularizedResidualObjective
        (twoHistoryResidualEnergy firstResidual secondResidual)
        residualScale regularization
        (twoHistoryCoefficient candidate) := by
  have denominator_pos :
      0 <
        (firstResidual - secondResidual) ^ 2 +
          2 * (regularization * residualScale) := by
    positivity
  have identity := twoHistory_objective_sub_at_solver
    firstResidual secondResidual residualScale regularization candidate
    denominator_pos.ne'
  nlinarith [sq_nonneg
    (candidate -
      twoHistoryRegularizedFirst firstResidual secondResidual
        residualScale regularization)]

/-- Two-history specialization of the source coefficient-amplification
bound, with the residual-scale premise made explicit. -/
theorem twoHistoryRegularized_coefficientEnergy_le
    (firstResidual secondResidual residualScale regularization : ℝ)
    (residualScale_pos : 0 < residualScale)
    (regularization_pos : 0 < regularization)
    (uniformResidual_le :
      twoHistoryResidualEnergy firstResidual secondResidual
          (uniformCoefficient 2) ≤ residualScale / 2) :
    coefficientEnergy
        (twoHistoryCoefficient
          (twoHistoryRegularizedFirst firstResidual secondResidual
            residualScale regularization)) ≤
      (1 + 1 / regularization) / 2 := by
  apply coefficientEnergy_le_of_regularized_minimizes
    (history_pos := by norm_num)
    (residualEnergy :=
      twoHistoryResidualEnergy firstResidual secondResidual)
    (residualScale := residualScale)
    (regularization := regularization)
    (coefficient :=
      twoHistoryCoefficient
        (twoHistoryRegularizedFirst firstResidual secondResidual
          residualScale regularization))
    regularization_pos residualScale_pos
    (twoHistoryResidualEnergy_nonneg _ _ _) uniformResidual_le
  have uniform_as_half :
      uniformCoefficient 2 = twoHistoryCoefficient (1 / 2) := by
    funext index
    fin_cases index <;> norm_num [uniformCoefficient, twoHistoryCoefficient]
  rw [uniform_as_half]
  exact twoHistoryRegularizedFirst_minimizes
    firstResidual secondResidual residualScale regularization (1 / 2)
    residualScale_pos regularization_pos

/-! ## Executable positive and negative boundaries -/

/-- Concrete nontrivial regularized mixture. -/
theorem twoHistory_regularized :
    twoHistoryRegularizedFirst 1 2 5 1 = 7 / 11 ∧
      coefficientEnergy
        (twoHistoryCoefficient
          (twoHistoryRegularizedFirst 1 2 5 1)) = 65 / 121 ∧
      coefficientEnergy
        (twoHistoryCoefficient
          (twoHistoryRegularizedFirst 1 2 5 1)) ≤
        (1 + 1 / (1 : ℝ)) / 2 := by
  norm_num [twoHistoryRegularizedFirst, coefficientEnergy,
    twoHistoryCoefficient, Fin.sum_univ_two]

/-- With zero regularization and identical residual columns, every affine
mixture has the same residual objective while coefficient energy grows
quadratically.  Thus no regularization-independent coefficient bound follows
from residual minimization alone. -/
theorem unregularized_identicalResiduals_unbounded (magnitude : ℝ) :
    regularizedResidualObjective
        (twoHistoryResidualEnergy 1 1) 2 0
        (twoHistoryCoefficient magnitude) = 1 ∧
      coefficientEnergy (twoHistoryCoefficient magnitude) =
        magnitude ^ 2 + (1 - magnitude) ^ 2 := by
  simp [regularizedResidualObjective, twoHistoryResidualEnergy,
    twoHistoryCoefficient_energy]

theorem unregularized_identicalResiduals_exceeds_any_bound
    (bound : ℝ) :
    ∃ coefficient : Fin 2 → ℝ,
      (∑ index, coefficient index = 1) ∧
      regularizedResidualObjective
          (twoHistoryResidualEnergy 1 1) 2 0 coefficient = 1 ∧
      bound < coefficientEnergy coefficient := by
  let magnitude := |bound| + 1
  refine ⟨twoHistoryCoefficient magnitude,
    twoHistoryCoefficient_sum magnitude, ?_, ?_⟩
  · exact (unregularized_identicalResiduals_unbounded magnitude).1
  · rw [(unregularized_identicalResiduals_unbounded magnitude).2]
    have hbound : bound < magnitude := by
      dsimp [magnitude]
      linarith [le_abs_self bound]
    have hmag_pos : 0 < magnitude := by
      dsimp [magnitude]
      positivity
    have hmag_ge_one : 1 ≤ magnitude := by
      dsimp [magnitude]
      linarith [abs_nonneg bound]
    have hsquare_ge : magnitude ≤ magnitude ^ 2 := by
      nlinarith [mul_nonneg hmag_pos.le (sub_nonneg.mpr hmag_ge_one)]
    nlinarith [sq_nonneg (1 - magnitude)]

#print axioms coefficientEnergy_le_of_regularized_minimizes
#print axioms twoHistory_objective_sub_at_solver
#print axioms twoHistoryRegularizedFirst_minimizes
#print axioms twoHistoryRegularized_coefficientEnergy_le
#print axioms twoHistory_regularized
#print axioms unregularized_identicalResiduals_exceeds_any_bound

end

end RegularizedResidualMixing

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
