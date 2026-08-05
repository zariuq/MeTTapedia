import Mathlib

/-!
# Affine fixed-point acceleration

Saad, *Acceleration methods for fixed point iterations*
(arXiv:2507.11746), distinguishes extrapolation of recent iterates from
fixed-point acceleration that also evaluates the fixed-point map.  Equations
(4)--(6) impose the common normalization that the combination coefficients
sum to one.

This file isolates that algebra over an arbitrary real normed vector space.
It proves that normalized combinations preserve every constant state and
every fixed point, gives the exact error identity and its absolute-weight
norm budget, and records two boundaries relevant to accelerated predictive
coding: non-normalized weights move fixed points, while normalized signed
weights can amplify error.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

noncomputable section

variable {ι V : Type*} [Fintype ι]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite linear combination of states. -/
def weightedCombination (coefficients : ι → ℝ) (states : ι → V) : V :=
  ∑ i, coefficients i • states i

/-- The normalization imposed by affine extrapolation and Anderson/Pulay
mixing: the coefficients sum to one. -/
def IsAffineWeights (coefficients : ι → ℝ) : Prop :=
  ∑ i, coefficients i = 1

/-- A fixed-point acceleration step that combines evaluations of the
fixed-point map, corresponding to equation (6) of the source. -/
def fixedPointAcceleratedStep
    (coefficients : ι → ℝ) (fixedPointMap : V → V)
    (states : ι → V) : V :=
  weightedCombination coefficients (fun i => fixedPointMap (states i))

theorem weightedCombination_add
    (coefficients : ι → ℝ) (left right : ι → V) :
    weightedCombination coefficients (fun i => left i + right i) =
      weightedCombination coefficients left +
        weightedCombination coefficients right := by
  simp [weightedCombination, smul_add, Finset.sum_add_distrib]

theorem weightedCombination_sub
    (coefficients : ι → ℝ) (left right : ι → V) :
    weightedCombination coefficients (fun i => left i - right i) =
      weightedCombination coefficients left -
        weightedCombination coefficients right := by
  simp [weightedCombination, smul_sub, Finset.sum_sub_distrib]

/-- Coefficients summing to one preserve every constant state. -/
theorem weightedCombination_const
    (coefficients : ι → ℝ) (state : V)
    (affine : IsAffineWeights coefficients) :
    weightedCombination coefficients (fun _ => state) = state := by
  rw [weightedCombination]
  rw [← Finset.sum_smul]
  simp only [IsAffineWeights] at affine
  rw [affine]
  simp

/-- The affine error identity: displacement from a reference state is the
same affine combination of the individual displacements. -/
theorem weightedCombination_sub_reference
    (coefficients : ι → ℝ) (states : ι → V) (reference : V)
    (affine : IsAffineWeights coefficients) :
    weightedCombination coefficients states - reference =
      weightedCombination coefficients (fun i => states i - reference) := by
  rw [weightedCombination_sub, weightedCombination_const coefficients reference affine]

/-- Signed extrapolation is controlled by the sum of absolute coefficient
weights, not by the affine normalization alone. -/
theorem norm_weightedCombination_sub_reference_le
    (coefficients : ι → ℝ) (states : ι → V) (reference : V)
    (affine : IsAffineWeights coefficients) :
    ‖weightedCombination coefficients states - reference‖ ≤
      ∑ i, |coefficients i| * ‖states i - reference‖ := by
  rw [weightedCombination_sub_reference coefficients states reference affine]
  calc
    ‖weightedCombination coefficients (fun i => states i - reference)‖
        ≤ ∑ i, ‖coefficients i • (states i - reference)‖ := by
          exact norm_sum_le _ _
    _ = ∑ i, |coefficients i| * ‖states i - reference‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs]

/-- With nonnegative affine weights, a uniform radius is preserved. -/
theorem norm_weightedCombination_sub_reference_le_radius
    (coefficients : ι → ℝ) (states : ι → V) (reference : V)
    (affine : IsAffineWeights coefficients)
    (nonnegative : ∀ i, 0 ≤ coefficients i)
    (radius : ℝ)
    (bounded : ∀ i, ‖states i - reference‖ ≤ radius) :
    ‖weightedCombination coefficients states - reference‖ ≤ radius := by
  calc
    ‖weightedCombination coefficients states - reference‖
        ≤ ∑ i, |coefficients i| * ‖states i - reference‖ :=
      norm_weightedCombination_sub_reference_le
        coefficients states reference affine
    _ ≤ ∑ i, coefficients i * radius := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_of_nonneg (nonnegative i)]
      exact mul_le_mul_of_nonneg_left (bounded i) (nonnegative i)
    _ = radius := by
      rw [← Finset.sum_mul]
      simp only [IsAffineWeights] at affine
      rw [affine]
      simp

/-- Every affine fixed-point acceleration step preserves a genuine fixed
point when all members of its window are already there. -/
theorem fixedPointAcceleratedStep_const
    (coefficients : ι → ℝ) (fixedPointMap : V → V) (fixedPoint : V)
    (affine : IsAffineWeights coefficients)
    (fixed : fixedPointMap fixedPoint = fixedPoint) :
    fixedPointAcceleratedStep coefficients fixedPointMap
      (fun _ => fixedPoint) =
      fixedPoint := by
  simp [fixedPointAcceleratedStep, fixed, weightedCombination_const,
    affine]

/-- A one-element acceleration window with unit weight is exactly the
ordinary fixed-point iteration. -/
theorem singleton_fixedPointAcceleratedStep
    (fixedPointMap : V → V) (state : V) :
    fixedPointAcceleratedStep (ι := Fin 1) (fun _ => 1)
      fixedPointMap (fun _ => state) =
      fixedPointMap state := by
  simp [fixedPointAcceleratedStep, weightedCombination]

/-! ## Sharp negative fixtures -/

def nonAffineWeights : Fin 2 → ℝ := ![1, 1]

def signedAffineWeights : Fin 2 → ℝ := ![2, -1]

def signedAffineStates : Fin 2 → ℝ := ![1, -1]

/-- Dropping the sum-to-one condition moves even a constant state. -/
theorem nonAffine_weights_move_constant :
    weightedCombination nonAffineWeights (fun _ : Fin 2 => (3 : ℝ)) = 6 ∧
      weightedCombination nonAffineWeights (fun _ : Fin 2 => (3 : ℝ)) ≠ 3 := by
  norm_num [weightedCombination, nonAffineWeights]

theorem signedAffineWeights_are_affine :
    IsAffineWeights signedAffineWeights := by
  norm_num [IsAffineWeights, signedAffineWeights]

/-- Affine normalization preserves constants but, without nonnegativity or
a safeguard, signed extrapolation can amplify errors by a factor three. -/
theorem signed_affine_weights_amplify :
    (∀ i, ‖signedAffineStates i‖ ≤ (1 : ℝ)) ∧
      ‖weightedCombination signedAffineWeights signedAffineStates‖ = 3 := by
  constructor
  · intro i
    fin_cases i <;> norm_num [signedAffineStates]
  · norm_num [weightedCombination, signedAffineWeights, signedAffineStates]

#print axioms weightedCombination_const
#print axioms weightedCombination_sub_reference
#print axioms norm_weightedCombination_sub_reference_le
#print axioms norm_weightedCombination_sub_reference_le_radius
#print axioms fixedPointAcceleratedStep_const
#print axioms singleton_fixedPointAcceleratedStep
#print axioms nonAffine_weights_move_constant
#print axioms signed_affine_weights_amplify

end

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
