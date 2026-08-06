import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditSpectralGeometry

/-!
# Metric-dependent steepest descent

Backpropagation supplies the gradient of the current scalar loss.  In the
Euclidean parameter metric, that gradient maximizes first-order decrease
among directions with no larger norm.  Consequently no alternative credit
rule can strictly improve that same local objective under the same norm
budget.

This does not make backpropagation optimal in every geometry.  A diagonal
linear readout gives an exact separation: the backpropagated credit has the
larger parameter-space first-order margin, while an inverse-Jacobian credit
is perfectly aligned with the desired output correction.  The two claims use
different metrics and are therefore compatible.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace MetricDependentSteepestDescent

open scoped InnerProductSpace
open SettledCreditSpectralGeometry

noncomputable section

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- First-order loss decrease obtained by stepping in `direction` against a
loss with gradient `gradient`. -/
def firstOrderDecrease (gradient direction : Parameter) : ℝ :=
  ⟪gradient, direction⟫_ℝ

/-- Backpropagation maximizes current-loss first-order decrease among all
directions with no larger Euclidean norm. -/
theorem firstOrderDecrease_le_bp_of_norm_le
    (gradient direction : Parameter)
    (norm_le : ‖direction‖ ≤ ‖gradient‖) :
    firstOrderDecrease gradient direction ≤
      firstOrderDecrease gradient gradient := by
  have inner_le_abs :
      ⟪gradient, direction⟫_ℝ ≤ |⟪gradient, direction⟫_ℝ| :=
    le_abs_self _
  have cauchy :
      |⟪gradient, direction⟫_ℝ| ≤ ‖gradient‖ * ‖direction‖ :=
    abs_real_inner_le_norm gradient direction
  have scaled :
      ‖gradient‖ * ‖direction‖ ≤ ‖gradient‖ * ‖gradient‖ :=
    mul_le_mul_of_nonneg_left norm_le (norm_nonneg gradient)
  unfold firstOrderDecrease
  rw [real_inner_self_eq_norm_sq]
  nlinarith

/-- Unless the candidate is exactly the backpropagated gradient, its
first-order decrease is strictly smaller under the same norm budget. -/
theorem firstOrderDecrease_lt_bp_of_norm_le_of_ne
    (gradient direction : Parameter)
    (norm_le : ‖direction‖ ≤ ‖gradient‖)
    (direction_ne : direction ≠ gradient) :
    firstOrderDecrease gradient direction <
      firstOrderDecrease gradient gradient := by
  have normSq_le : ‖direction‖ ^ 2 ≤ ‖gradient‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg direction) (norm_nonneg gradient)).2 norm_le
  have difference_ne : gradient - direction ≠ 0 :=
    sub_ne_zero.mpr direction_ne.symm
  have difference_normSq_pos : 0 < ‖gradient - direction‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr difference_ne)
  rw [norm_sub_sq_real] at difference_normSq_pos
  unfold firstOrderDecrease
  rw [real_inner_self_eq_norm_sq]
  nlinarith

/-- Pointwise no-go: under the same Euclidean direction budget there is no
credit with strictly larger current-loss first-order decrease than BP. -/
theorem not_exists_strictly_better_than_bp_under_norm_budget
    (gradient : Parameter) :
    ¬ ∃ direction : Parameter,
      ‖direction‖ ≤ ‖gradient‖ ∧
        firstOrderDecrease gradient gradient <
          firstOrderDecrease gradient direction := by
  rintro ⟨direction, norm_le, better⟩
  have bound := firstOrderDecrease_le_bp_of_norm_le gradient direction norm_le
  exact (not_lt_of_ge bound) better

/-- A rule cannot strictly dominate backpropagation at every gradient while
respecting the same Euclidean direction budget. -/
theorem not_exists_rule_strictly_dominates_bp :
    ¬ ∃ rule : Parameter → Parameter,
      ∀ gradient,
        ‖rule gradient‖ ≤ ‖gradient‖ ∧
          firstOrderDecrease gradient gradient <
            firstOrderDecrease gradient (rule gradient) := by
  rintro ⟨rule, dominates⟩
  exact not_exists_strictly_better_than_bp_under_norm_budget (0 : Parameter)
    ⟨rule 0, (dominates 0).1, (dominates 0).2⟩

/-! ## Output-space geometry -/

variable {ι : Type*} [Fintype ι]

/-- Output change of a diagonal linear readout. -/
def diagonalOutputChange
    (gain direction : ι → ℝ) : ι → ℝ :=
  diagonalScale gain direction

/-- Parameter-space backpropagated credit for a diagonal readout and output
residual.  The readout is self-adjoint in these coordinates. -/
def diagonalBPCredit (gain residual : ι → ℝ) : ι → ℝ :=
  diagonalScale gain residual

/-- Credit that directly inverts a nonzero diagonal readout so its induced
output change equals the requested residual. -/
def inverseDiagonalTargetCredit
    (gain residual : ι → ℝ) : ι → ℝ :=
  fun index => residual index / gain index

omit [Fintype ι] in
/-- Inverse-Jacobian credit realizes the requested output correction exactly
when every active diagonal gain is nonzero. -/
theorem diagonalOutputChange_inverseDiagonalTargetCredit
    (gain residual : ι → ℝ)
    (gain_ne_zero : ∀ index, gain index ≠ 0) :
    diagonalOutputChange gain
        (inverseDiagonalTargetCredit gain residual) = residual := by
  funext index
  simp only [diagonalOutputChange, inverseDiagonalTargetCredit,
    diagonalScale_apply]
  exact mul_div_cancel₀ (residual index) (gain_ne_zero index)

/-- Hence inverse-Jacobian credit has target alignment one for every nonzero
residual. -/
theorem inverseDiagonalTargetCredit_cosine_eq_one
    (gain residual : ι → ℝ)
    (gain_ne_zero : ∀ index, gain index ≠ 0)
    (residual_normSq_pos : 0 < coordinateNormSq residual) :
    coordinateCosine
        (diagonalOutputChange gain
          (inverseDiagonalTargetCredit gain residual)) residual = 1 := by
  rw [diagonalOutputChange_inverseDiagonalTargetCredit gain residual
    gain_ne_zero]
  simpa using coordinateCosine_pos_smul_self residual 1 zero_lt_one
    residual_normSq_pos

/-! ## A strict metric-separation witness -/

namespace DiagonalWitness

def gain : Fin 2 → ℝ := ![1, 2]

def residual : Fin 2 → ℝ := ![1, 1]

def bpCredit : Fin 2 → ℝ := diagonalBPCredit gain residual

def targetCredit : Fin 2 → ℝ :=
  inverseDiagonalTargetCredit gain residual

def bpOutputChange : Fin 2 → ℝ :=
  diagonalOutputChange gain bpCredit

def targetOutputChange : Fin 2 → ℝ :=
  diagonalOutputChange gain targetCredit

theorem bpCredit_eq : bpCredit = ![1, 2] := by
  funext index
  fin_cases index <;>
    norm_num [bpCredit, diagonalBPCredit, diagonalScale, gain, residual]

theorem targetCredit_eq : targetCredit = ![1, 1 / 2] := by
  funext index
  fin_cases index <;>
    norm_num [targetCredit, inverseDiagonalTargetCredit, gain, residual]

theorem bpOutputChange_eq : bpOutputChange = ![1, 4] := by
  funext index
  fin_cases index <;>
    norm_num [bpOutputChange, diagonalOutputChange, bpCredit,
      diagonalBPCredit, diagonalScale, gain, residual]

theorem targetOutputChange_eq : targetOutputChange = residual := by
  apply diagonalOutputChange_inverseDiagonalTargetCredit
  intro index
  fin_cases index <;> norm_num [gain]

theorem residual_normSq : coordinateNormSq residual = 2 := by
  norm_num [coordinateNormSq_apply, residual, Fin.sum_univ_two]

/-- The inverse credit is perfectly aligned with the requested output
change. -/
theorem targetCredit_targetAlignment_eq_one :
    coordinateCosine targetOutputChange residual = 1 := by
  rw [targetOutputChange_eq]
  simpa [residual_normSq] using
    coordinateCosine_pos_smul_self residual 1 zero_lt_one
      (by rw [residual_normSq]; norm_num)

/-- Backpropagation is strictly misaligned in output space for the anisotropic
readout. -/
theorem bpCredit_targetAlignment_lt_one :
    coordinateCosine bpOutputChange residual < 1 := by
  have root_pos : 0 < Real.sqrt (34 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have five_lt_root : (5 : ℝ) < Real.sqrt 34 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  rw [coordinateCosine, bpOutputChange_eq]
  norm_num [coordinateInner, coordinateNormSq, residual, Fin.sum_univ_two]
  exact (div_lt_one root_pos).2 five_lt_root

/-- Nevertheless BP has the strictly larger current-loss first-order margin
in parameter space. -/
theorem targetCredit_parameterMargin_lt_bp :
    coordinateInner bpCredit targetCredit <
      coordinateInner bpCredit bpCredit := by
  rw [bpCredit_eq, targetCredit_eq]
  norm_num [coordinateInner, Fin.sum_univ_two]

/-- Positive separation fixture: output-space alignment prefers the target
credit while Euclidean parameter-space steepest descent prefers BP. -/
theorem targetAlignment_and_parameterDescent_rank_differently :
    coordinateCosine targetOutputChange residual = 1 ∧
      coordinateCosine bpOutputChange residual < 1 ∧
      coordinateInner bpCredit targetCredit <
        coordinateInner bpCredit bpCredit := by
  exact ⟨targetCredit_targetAlignment_eq_one,
    bpCredit_targetAlignment_lt_one,
    targetCredit_parameterMargin_lt_bp⟩

/-- Negative boundary: with an isotropic readout, BP induces a positive
multiple of the target residual, so there is no target-alignment advantage. -/
theorem isotropicReadout_bp_targetAlignment_eq_one
    (scale : ℝ) (scale_pos : 0 < scale)
    (value : Fin 2 → ℝ)
    (value_normSq_pos : 0 < coordinateNormSq value) :
    coordinateCosine
        (diagonalOutputChange (fun _ => scale)
          (diagonalBPCredit (fun _ => scale) value)) value = 1 := by
  have output_eq :
      diagonalOutputChange (fun _ : Fin 2 => scale)
          (diagonalBPCredit (fun _ => scale) value) =
        (scale ^ 2) • value := by
    funext index
    simp [diagonalOutputChange, diagonalBPCredit, diagonalScale]
    ring
  rw [output_eq]
  exact coordinateCosine_pos_smul_self value (scale ^ 2)
    (sq_pos_of_pos scale_pos) value_normSq_pos

end DiagonalWitness

#print axioms firstOrderDecrease_le_bp_of_norm_le
#print axioms firstOrderDecrease_lt_bp_of_norm_le_of_ne
#print axioms not_exists_strictly_better_than_bp_under_norm_budget
#print axioms not_exists_rule_strictly_dominates_bp
#print axioms inverseDiagonalTargetCredit_cosine_eq_one
#print axioms DiagonalWitness.targetAlignment_and_parameterDescent_rank_differently
#print axioms DiagonalWitness.isotropicReadout_bp_targetAlignment_eq_one

end

end MetricDependentSteepestDescent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
