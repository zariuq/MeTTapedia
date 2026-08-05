import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Finite maximal-update width scaling

Yang et al., *Tensor Programs V: Tuning Large Neural Networks via Zero-Shot
Hyperparameter Transfer* (arXiv:2203.03466), motivate maximal-update
parameterization with a one-hidden-layer linear network

`f(x) = Vᵀ U x`.

After simultaneous updates of `V` in the direction of `U` and `U` in the
direction of `V`, the output contains four exact terms.  Under standard
one-step scaling, the term proportional to `UᵀU` grows with width.  Under the
source's maximal-update statistics and reciprocal layerwise rates, the
`UᵀU` and `VᵀV` contributions are both width independent.

This file proves the finite vector identity, the two statistics-level
specializations, strict growth across widths for the standard specialization,
width invariance for the maximal-update specialization, and rational
four-coordinate fixtures realizing both regimes.  It does not formalize the
source's random initialization, law-of-large-numbers limit, uniqueness of
maximal-update parameterization, optimizer generalization, hyperparameter
optimality, or empirical zero-shot transfer.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

namespace MaximalUpdateScaling

open scoped BigOperators

/-- Scalar output of a one-hidden-layer linear network with scalar input. -/
def twoLayerLinearOutput {width : ℕ}
    (outputWeight inputWeight : Fin width → ℝ) (input : ℝ) : ℝ :=
  (outputWeight ⬝ᵥ inputWeight) * input

/-- Simultaneous one-step update of the output weights. -/
def updateOutputWeight {width : ℕ}
    (outputWeight inputWeight : Fin width → ℝ)
    (signal outputRate : ℝ) : Fin width → ℝ :=
  outputWeight + (outputRate * signal) • inputWeight

/-- Simultaneous one-step update of the input weights. -/
def updateInputWeight {width : ℕ}
    (outputWeight inputWeight : Fin width → ℝ)
    (signal inputRate : ℝ) : Fin width → ℝ :=
  inputWeight + (inputRate * signal) • outputWeight

/-- The exact four-term output after the simultaneous update. -/
theorem twoLayerLinearOutput_after_update
    {width : ℕ} (outputWeight inputWeight : Fin width → ℝ)
    (input signal outputRate inputRate : ℝ) :
    twoLayerLinearOutput
        (updateOutputWeight outputWeight inputWeight signal outputRate)
        (updateInputWeight outputWeight inputWeight signal inputRate)
        input =
      ((outputWeight ⬝ᵥ inputWeight) +
          inputRate * signal * (outputWeight ⬝ᵥ outputWeight) +
          outputRate * signal * (inputWeight ⬝ᵥ inputWeight) +
          outputRate * inputRate * signal ^ 2 *
            (outputWeight ⬝ᵥ inputWeight)) * input := by
  simp only [twoLayerLinearOutput, updateOutputWeight, updateInputWeight,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
  rw [dotProduct_comm inputWeight outputWeight]
  ring

/-- Statistics-level standard-scaling coefficient.  The cross statistic is
zero, the input-weight squared norm is `width`, both layerwise rates are one,
and the output-weight squared norm is one. -/
def standardOneStepOutput
    (width : ℕ) (input signal : ℝ) : ℝ :=
  (signal * ((width : ℝ) + 1)) * input

/-- Statistics-level maximal-update coefficient.  The output-weight squared
norm is `1 / width`, while the output- and input-layer rates are reciprocal
`1 / width` and `width`. -/
def maximalUpdateOneStepOutput
    (input signal : ℝ) : ℝ :=
  (2 * signal) * input

/-- Orthogonal weights with standard squared norms specialize the vector
identity to a coefficient growing linearly with width. -/
theorem standard_statistics_after_update
    {width : ℕ} (outputWeight inputWeight : Fin width → ℝ)
    (input signal : ℝ)
    (hcross : outputWeight ⬝ᵥ inputWeight = 0)
    (hinput : inputWeight ⬝ᵥ inputWeight = (width : ℝ))
    (houtput : outputWeight ⬝ᵥ outputWeight = 1) :
    twoLayerLinearOutput
        (updateOutputWeight outputWeight inputWeight signal 1)
        (updateInputWeight outputWeight inputWeight signal 1)
        input =
      standardOneStepOutput width input signal := by
  rw [twoLayerLinearOutput_after_update, hcross, hinput, houtput]
  unfold standardOneStepOutput
  ring

/-- The source's maximal-update statistics and reciprocal rates give the
width-independent coefficient `2 * signal`. -/
theorem maximal_update_statistics_after_update
    {width : ℕ} (outputWeight inputWeight : Fin width → ℝ)
    (input signal : ℝ) (hwidth : 0 < width)
    (hcross : outputWeight ⬝ᵥ inputWeight = 0)
    (hinput : inputWeight ⬝ᵥ inputWeight = (width : ℝ))
    (houtput : outputWeight ⬝ᵥ outputWeight = 1 / (width : ℝ)) :
    twoLayerLinearOutput
        (updateOutputWeight outputWeight inputWeight signal
          (1 / (width : ℝ)))
        (updateInputWeight outputWeight inputWeight signal (width : ℝ))
        input =
      maximalUpdateOneStepOutput input signal := by
  have hwidthReal : (width : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwidth)
  rw [twoLayerLinearOutput_after_update, hcross, hinput, houtput]
  unfold maximalUpdateOneStepOutput
  field_simp [hwidthReal]
  ring

/-- At positive input-signal product, the standard statistics-level output
strictly increases with width. -/
theorem standardOneStepOutput_strictMono_width
    {smaller larger : ℕ} (input signal : ℝ)
    (hwidth : smaller < larger) (hpositive : 0 < signal * input) :
    standardOneStepOutput smaller input signal <
      standardOneStepOutput larger input signal := by
  have hwidthReal : (smaller : ℝ) < larger := by
    exact_mod_cast hwidth
  unfold standardOneStepOutput
  nlinarith

/-- Any two actual finite networks satisfying the maximal-update statistics
have the same one-step output, independently of their positive widths. -/
theorem maximal_update_statistics_width_invariant
    {firstWidth secondWidth : ℕ}
    (firstOutput firstInput : Fin firstWidth → ℝ)
    (secondOutput secondInput : Fin secondWidth → ℝ)
    (input signal : ℝ)
    (hfirstWidth : 0 < firstWidth) (hsecondWidth : 0 < secondWidth)
    (hfirstCross : firstOutput ⬝ᵥ firstInput = 0)
    (hfirstInput : firstInput ⬝ᵥ firstInput = (firstWidth : ℝ))
    (hfirstOutput :
      firstOutput ⬝ᵥ firstOutput = 1 / (firstWidth : ℝ))
    (hsecondCross : secondOutput ⬝ᵥ secondInput = 0)
    (hsecondInput : secondInput ⬝ᵥ secondInput = (secondWidth : ℝ))
    (hsecondOutput :
      secondOutput ⬝ᵥ secondOutput = 1 / (secondWidth : ℝ)) :
    twoLayerLinearOutput
        (updateOutputWeight firstOutput firstInput signal
          (1 / (firstWidth : ℝ)))
        (updateInputWeight firstOutput firstInput signal (firstWidth : ℝ))
        input =
      twoLayerLinearOutput
        (updateOutputWeight secondOutput secondInput signal
          (1 / (secondWidth : ℝ)))
        (updateInputWeight secondOutput secondInput signal (secondWidth : ℝ))
        input := by
  rw [maximal_update_statistics_after_update _ _ input signal hfirstWidth
      hfirstCross hfirstInput hfirstOutput,
    maximal_update_statistics_after_update _ _ input signal hsecondWidth
      hsecondCross hsecondInput hsecondOutput]

/-- A rational width-four input-weight vector with squared norm four. -/
def widthFourInputWeight : Fin 4 → ℝ :=
  ![1, 1, 1, 1]

/-- A rational width-four output-weight vector with squared norm one,
orthogonal to `widthFourInputWeight`. -/
noncomputable def widthFourStandardOutputWeight : Fin 4 → ℝ :=
  ![(1 : ℝ) / 2, -(1 : ℝ) / 2, (1 : ℝ) / 2, -(1 : ℝ) / 2]

/-- A rational width-four output-weight vector with squared norm `1 / 4`,
orthogonal to `widthFourInputWeight`. -/
noncomputable def widthFourMaximalOutputWeight : Fin 4 → ℝ :=
  ![(1 : ℝ) / 4, -(1 : ℝ) / 4, (1 : ℝ) / 4, -(1 : ℝ) / 4]

theorem widthFour_standard_statistics :
    widthFourStandardOutputWeight ⬝ᵥ widthFourInputWeight = 0 ∧
      widthFourInputWeight ⬝ᵥ widthFourInputWeight = 4 ∧
      widthFourStandardOutputWeight ⬝ᵥ
          widthFourStandardOutputWeight = 1 := by
  norm_num [widthFourStandardOutputWeight, widthFourInputWeight, dotProduct,
    Fin.sum_univ_succ]

theorem widthFour_maximal_statistics :
    widthFourMaximalOutputWeight ⬝ᵥ widthFourInputWeight = 0 ∧
      widthFourInputWeight ⬝ᵥ widthFourInputWeight = 4 ∧
      widthFourMaximalOutputWeight ⬝ᵥ
          widthFourMaximalOutputWeight = (1 : ℝ) / 4 := by
  norm_num [widthFourMaximalOutputWeight, widthFourInputWeight, dotProduct,
    Fin.sum_univ_succ]

/-- Standard scaling turns the width-four rational fixture's zero initial
output into five after a unit signal and unit input. -/
theorem widthFour_standard_update :
    twoLayerLinearOutput
        (updateOutputWeight widthFourStandardOutputWeight
          widthFourInputWeight 1 1)
        (updateInputWeight widthFourStandardOutputWeight
          widthFourInputWeight 1 1)
        1 = 5 := by
  rcases widthFour_standard_statistics with ⟨hcross, hinput, houtput⟩
  rw [standard_statistics_after_update _ _ 1 1 hcross hinput houtput]
  norm_num [standardOneStepOutput]

/-- Maximal-update scaling turns the corresponding width-four fixture's zero
initial output into two rather than five. -/
theorem widthFour_maximal_update :
    twoLayerLinearOutput
        (updateOutputWeight widthFourMaximalOutputWeight
          widthFourInputWeight 1 ((1 : ℝ) / 4))
        (updateInputWeight widthFourMaximalOutputWeight
          widthFourInputWeight 1 (4 : ℝ))
        1 = 2 := by
  rcases widthFour_maximal_statistics with ⟨hcross, hinput, houtput⟩
  rw [twoLayerLinearOutput_after_update, hcross, hinput, houtput]
  norm_num

/-- The two fixtures start at the same zero output, so their post-update
difference is not an initialization-output artifact. -/
theorem widthFour_initial_outputs_agree :
    twoLayerLinearOutput widthFourStandardOutputWeight
        widthFourInputWeight 1 = 0 ∧
      twoLayerLinearOutput widthFourMaximalOutputWeight
        widthFourInputWeight 1 = 0 := by
  rcases widthFour_standard_statistics with ⟨hstandard, _, _⟩
  rcases widthFour_maximal_statistics with ⟨hmaximal, _, _⟩
  simp [twoLayerLinearOutput, hstandard, hmaximal]

#print axioms twoLayerLinearOutput_after_update
#print axioms standard_statistics_after_update
#print axioms maximal_update_statistics_after_update
#print axioms standardOneStepOutput_strictMono_width
#print axioms maximal_update_statistics_width_invariant
#print axioms widthFour_standard_statistics
#print axioms widthFour_maximal_statistics
#print axioms widthFour_standard_update
#print axioms widthFour_maximal_update
#print axioms widthFour_initial_outputs_agree

end MaximalUpdateScaling

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
