import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Transfer, interference, and the finite-step boundary

Riemer et al., *Learning to Learn without Forgetting by Maximizing Transfer
and Minimizing Interference* (arXiv:1810.11910), classify a pair of examples
by the sign of the inner product of their loss gradients.  Positive alignment
is called transfer and negative alignment is called interference.

That sign is a first-order statement.  This file recovers it inside an exact
finite-step model and exposes the missing step-size boundary.  For a
half-squared-distance retention loss, a step along another example's gradient
changes the retained loss by

`- rate * alignment + rate^2 * ‖direction‖^2 / 2`.

Positive alignment therefore supplies a nonempty interval of transferring
step sizes, but it does not make every positive step safe.  Negative alignment
causes strict finite interference at every positive step.  Small-step and
large-step scalar fixtures separate the two readings.

The source's Meta-Experience Replay sampling process, Reptile approximation,
reservoir distribution, second-order meta-objective, and empirical results are
not formalized here.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace TransferInterferenceBoundary

noncomputable section

open scoped InnerProductSpace

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- Isotropic quadratic loss centered at `target`. -/
def halfSquaredDistance (target parameter : Parameter) : ℝ :=
  ‖parameter - target‖ ^ 2 / 2

/-- Exact gradient of `halfSquaredDistance` at `parameter`. -/
def quadraticGradient (target parameter : Parameter) : Parameter :=
  parameter - target

/-- A finite gradient-style step along an externally supplied direction. -/
def gradientStep
    (parameter direction : Parameter) (rate : ℝ) : Parameter :=
  parameter - rate • direction

/-- Pairwise gradient alignment used by the source to distinguish transfer
from interference. -/
def pairAlignment (first second : Parameter) : ℝ :=
  ⟪first, second⟫_ℝ

/-- Exact finite-step loss change.  The first term is the source's alignment
criterion and the second is the complete isotropic curvature correction. -/
theorem halfSquaredDistance_gradientStep_change_exact
    (target parameter direction : Parameter) (rate : ℝ) :
    halfSquaredDistance target (gradientStep parameter direction rate) -
        halfSquaredDistance target parameter =
      -rate * pairAlignment (quadraticGradient target parameter) direction +
        rate ^ 2 * ‖direction‖ ^ 2 / 2 := by
  unfold halfSquaredDistance gradientStep pairAlignment quadraticGradient
  rw [show parameter - rate • direction - target =
      (parameter - target) - rate • direction by abel]
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right]
  rw [mul_pow, sq_abs]
  ring

/-- At a positive learning rate, exact transfer occurs precisely when the
first-order alignment exceeds the finite curvature budget. -/
theorem halfSquaredDistance_gradientStep_lt_iff
    (target parameter direction : Parameter) {rate : ℝ}
    (hrate : 0 < rate) :
    halfSquaredDistance target (gradientStep parameter direction rate) <
        halfSquaredDistance target parameter ↔
      rate * ‖direction‖ ^ 2 / 2 <
        pairAlignment (quadraticGradient target parameter) direction := by
  rw [← sub_neg]
  rw [halfSquaredDistance_gradientStep_change_exact]
  constructor <;> intro h <;> nlinarith

/-- The source's positive-alignment condition is locally sound: it always
admits a strictly positive finite step that transfers. -/
theorem positive_alignment_has_safe_finite_step
    (target parameter direction : Parameter)
    (halignment :
      0 < pairAlignment (quadraticGradient target parameter) direction) :
    ∃ rate : ℝ, 0 < rate ∧
      halfSquaredDistance target (gradientStep parameter direction rate) <
        halfSquaredDistance target parameter := by
  have hdirection : direction ≠ 0 := by
    intro hzero
    subst direction
    simp [pairAlignment] at halignment
  have hnormSq : 0 < ‖direction‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hdirection)
  let rate :=
    pairAlignment (quadraticGradient target parameter) direction /
      ‖direction‖ ^ 2
  have hrate : 0 < rate := div_pos halignment hnormSq
  refine ⟨rate, hrate, ?_⟩
  apply (halfSquaredDistance_gradientStep_lt_iff
    target parameter direction hrate).2
  have hcancel :
      rate * ‖direction‖ ^ 2 =
        pairAlignment (quadraticGradient target parameter) direction := by
    exact div_mul_cancel₀ _ (ne_of_gt hnormSq)
  nlinarith

/-- Negative pairwise alignment implies strict finite interference for every
positive step; the curvature term cannot rescue it. -/
theorem negative_alignment_strictly_interferes
    (target parameter direction : Parameter) {rate : ℝ}
    (hrate : 0 < rate)
    (halignment :
      pairAlignment (quadraticGradient target parameter) direction < 0) :
    halfSquaredDistance target parameter <
      halfSquaredDistance target (gradientStep parameter direction rate) := by
  rw [← sub_pos]
  rw [halfSquaredDistance_gradientStep_change_exact]
  have hnormSq : 0 ≤ ‖direction‖ ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg rate]

/-- Positive fixture: unit alignment and a unit step reach the quadratic
optimum and strictly lower the retained loss. -/
theorem unit_alignment_unit_step_transfers :
    0 < pairAlignment (quadraticGradient (0 : ℝ) 1) 1 ∧
      halfSquaredDistance (0 : ℝ) (gradientStep 1 1 1) <
        halfSquaredDistance (0 : ℝ) 1 := by
  norm_num [pairAlignment, quadraticGradient, gradientStep,
    halfSquaredDistance, Real.norm_eq_abs]

/-- Negative fixture: the same positive alignment does not license an
arbitrary finite step.  A rate of three overshoots and strictly increases the
retained quadratic loss. -/
theorem positive_alignment_large_step_interferes :
    0 < pairAlignment (quadraticGradient (0 : ℝ) 1) 1 ∧
      halfSquaredDistance (0 : ℝ) 1 <
        halfSquaredDistance (0 : ℝ) (gradientStep 1 1 3) := by
  norm_num [pairAlignment, quadraticGradient, gradientStep,
    halfSquaredDistance, Real.norm_eq_abs]

#print axioms halfSquaredDistance_gradientStep_change_exact
#print axioms halfSquaredDistance_gradientStep_lt_iff
#print axioms positive_alignment_has_safe_finite_step
#print axioms negative_alignment_strictly_interferes
#print axioms unit_alignment_unit_step_transfers
#print axioms positive_alignment_large_step_interferes

end

end TransferInterferenceBoundary

end Mettapedia.MachineLearning.ContinualLearning
