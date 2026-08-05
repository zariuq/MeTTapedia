import Mathlib

/-!
# Dynamic hypernetwork row scaling

Ha, Dai, and Le, *HyperNetworks* (arXiv:1609.09106), Equations (7)--(8),
replace full dynamic matrix generation by a memory-efficient construction that
scales each row of a fixed matrix with a dynamically generated coefficient.

This file gives finite exact-real semantics for that construction.  Applying a
row-scaled matrix is exactly pointwise scaling of the base matrix-vector
product.  The source's two-path recurrent preactivation is recovered by
applying the construction independently to hidden and input matrices.  Unit
scales recover the fixed network, while zero scales leave only the generated
bias.

Row scaling is not arbitrary matrix generation.  It preserves every
within-row proportionality relation of the base matrix.  A two-column fixture
therefore proves that a row `[1, 1]` cannot be dynamically changed into
`[1, 0]` by any scalar row gate.

No theorem here claims parameter savings for a concrete implementation,
learnability of the scale generator, gradient improvement, or the source's
empirical results.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace DynamicHypernetwork

noncomputable section

variable {Row Column Hidden Input : Type*}

/-- Equation (7): multiply every entry in one base-matrix row by the same
dynamically generated row coefficient. -/
def rowScaledMatrix
    (scale : Row → ℝ) (weight : Row → Column → ℝ) :
    Row → Column → ℝ :=
  fun row column => scale row * weight row column

/-- Finite matrix-vector application. -/
def matrixVector [Fintype Column]
    (weight : Row → Column → ℝ) (input : Column → ℝ) :
    Row → ℝ :=
  fun row => ∑ column, weight row column * input column

/-- Applying Equation (7) is exactly pointwise scaling of the base
matrix-vector product. -/
theorem matrixVector_rowScaledMatrix [Fintype Column]
    (scale : Row → ℝ) (weight : Row → Column → ℝ)
    (input : Column → ℝ) (row : Row) :
    matrixVector (rowScaledMatrix scale weight) input row =
      scale row * matrixVector weight input row := by
  simp [matrixVector, rowScaledMatrix, Finset.mul_sum, mul_assoc]

/-- Unit row coefficients recover the fixed base matrix exactly. -/
@[simp] theorem rowScaledMatrix_one
    (weight : Row → Column → ℝ) :
    rowScaledMatrix (fun _ => 1) weight = weight := by
  funext row column
  simp [rowScaledMatrix]

/-- Zero row coefficients erase the generated matrix path exactly. -/
@[simp] theorem rowScaledMatrix_zero
    (weight : Row → Column → ℝ) :
    rowScaledMatrix (fun _ => 0) weight = fun _ _ => 0 := by
  funext row column
  simp [rowScaledMatrix]

/-- The finite preactivation of Equation (8), with separately generated row
scales for the hidden-state and input paths. -/
def hyperPreactivation [Fintype Hidden] [Fintype Input]
    (hiddenScale inputScale : Row → ℝ)
    (hiddenWeight : Row → Hidden → ℝ)
    (inputWeight : Row → Input → ℝ)
    (bias : Row → ℝ)
    (hidden : Hidden → ℝ)
    (input : Input → ℝ) :
    Row → ℝ :=
  fun row =>
    matrixVector (rowScaledMatrix hiddenScale hiddenWeight) hidden row +
      matrixVector (rowScaledMatrix inputScale inputWeight) input row +
      bias row

/-- Exact source-form recovery: the generated-matrix form equals pointwise
scaling of the two fixed matrix-vector products. -/
theorem hyperPreactivation_eq_source [Fintype Hidden] [Fintype Input]
    (hiddenScale inputScale : Row → ℝ)
    (hiddenWeight : Row → Hidden → ℝ)
    (inputWeight : Row → Input → ℝ)
    (bias : Row → ℝ)
    (hidden : Hidden → ℝ)
    (input : Input → ℝ)
    (row : Row) :
    hyperPreactivation hiddenScale inputScale hiddenWeight inputWeight
        bias hidden input row =
      hiddenScale row * matrixVector hiddenWeight hidden row +
        inputScale row * matrixVector inputWeight input row +
        bias row := by
  simp [hyperPreactivation, matrixVector_rowScaledMatrix]

/-- Unit dynamic scales recover the ordinary fixed-weight recurrent
preactivation. -/
theorem hyperPreactivation_one [Fintype Hidden] [Fintype Input]
    (hiddenWeight : Row → Hidden → ℝ)
    (inputWeight : Row → Input → ℝ)
    (bias : Row → ℝ)
    (hidden : Hidden → ℝ)
    (input : Input → ℝ)
    (row : Row) :
    hyperPreactivation (fun _ => 1) (fun _ => 1)
        hiddenWeight inputWeight bias hidden input row =
      matrixVector hiddenWeight hidden row +
        matrixVector inputWeight input row +
        bias row := by
  simp [hyperPreactivation_eq_source]

/-- Zero dynamic scales leave only the bias path. -/
theorem hyperPreactivation_zero [Fintype Hidden] [Fintype Input]
    (hiddenWeight : Row → Hidden → ℝ)
    (inputWeight : Row → Input → ℝ)
    (bias : Row → ℝ)
    (hidden : Hidden → ℝ)
    (input : Input → ℝ)
    (row : Row) :
    hyperPreactivation (fun _ => 0) (fun _ => 0)
        hiddenWeight inputWeight bias hidden input row =
      bias row := by
  simp [hyperPreactivation_eq_source]

/-- Row scaling preserves the cross-product relation between every pair of
entries in a base row.  This is the exact algebraic expressivity boundary. -/
theorem rowScaledMatrix_preserves_row_proportionality
    (scale : Row → ℝ) (weight : Row → Column → ℝ)
    (row : Row) (first second : Column) :
    rowScaledMatrix scale weight row first * weight row second =
      rowScaledMatrix scale weight row second * weight row first := by
  simp [rowScaledMatrix]
  ring

/-! ## Executable positive and negative fixtures -/

def scalarWeight : Fin 1 → Fin 1 → ℝ :=
  fun _row _column => 2

def scalarInput : Fin 1 → ℝ :=
  fun _column => 3

theorem dynamic_scale_changes_generated_action :
    matrixVector (rowScaledMatrix (fun _ : Fin 1 => 2) scalarWeight)
        scalarInput 0 = 12 ∧
      matrixVector (rowScaledMatrix (fun _ : Fin 1 => 1) scalarWeight)
        scalarInput 0 = 6 := by
  norm_num [matrixVector, rowScaledMatrix, scalarWeight, scalarInput]

def repeatedRowWeight : Fin 1 → Fin 2 → ℝ :=
  fun _row _column => 1

def unequalTargetRow : Fin 1 → Fin 2 → ℝ
  | _, 0 => 1
  | _, 1 => 0

/-- A scalar row gate cannot independently edit two columns of the same row. -/
theorem unequalTargetRow_not_rowScaled :
    ¬ ∃ scale : Fin 1 → ℝ,
      rowScaledMatrix scale repeatedRowWeight = unequalTargetRow := by
  rintro ⟨scale, generated⟩
  have first := congrFun (congrFun generated 0) 0
  have second := congrFun (congrFun generated 0) 1
  norm_num [rowScaledMatrix, repeatedRowWeight, unequalTargetRow] at first second
  linarith

#print axioms matrixVector_rowScaledMatrix
#print axioms rowScaledMatrix_one
#print axioms rowScaledMatrix_zero
#print axioms hyperPreactivation_eq_source
#print axioms hyperPreactivation_one
#print axioms hyperPreactivation_zero
#print axioms rowScaledMatrix_preserves_row_proportionality
#print axioms dynamic_scale_changes_generated_action
#print axioms unequalTargetRow_not_rowScaled

end

end DynamicHypernetwork

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
