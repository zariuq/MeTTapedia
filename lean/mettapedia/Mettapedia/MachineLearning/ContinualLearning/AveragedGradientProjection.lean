import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-!
# Averaged episodic-gradient projection

Chaudhry, Ranzato, Rohrbach, and Elhoseiny (2019), *Efficient Lifelong
Learning with A-GEM*, replace the family of GEM replay constraints by one
average replay-gradient half-space.  When a proposed gradient conflicts with
the replay gradient, their Equation (11) subtracts its component along the
replay gradient.

This file proves that closed form feasible, idempotent, and globally closest
in Euclidean distance among all directions satisfying the averaged
first-order retention constraint.  It also states the finite-step curvature
condition needed to turn that first-order constraint into a genuine
non-increase of replay loss.  An explicit stationary-point counterexample
shows that the latter condition cannot be omitted.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace AveragedGradientProjection

noncomputable section

open scoped InnerProductSpace

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- The A-GEM first-order half-space: the proposed descent direction has
nonnegative alignment with the replay gradient. -/
def Feasible (reference direction : Parameter) : Prop :=
  0 ≤ ⟪reference, direction⟫_ℝ

/-- Closed-form projection from A-GEM Equation (11).  The nonconflicting
branch is kept exactly; the conflicting branch removes the component along
the reference gradient. -/
def project (proposed reference : Parameter) : Parameter :=
  if 0 ≤ ⟪reference, proposed⟫_ℝ then
    proposed
  else
    proposed -
      (⟪reference, proposed⟫_ℝ / ‖reference‖ ^ 2) • reference

@[simp] theorem project_of_feasible
    (proposed reference : Parameter)
    (hfeasible : Feasible reference proposed) :
    project proposed reference = proposed := by
  unfold Feasible at hfeasible
  simp only [project, if_pos hfeasible]

theorem project_of_conflict
    (proposed reference : Parameter)
    (hconflict : ⟪reference, proposed⟫_ℝ < 0) :
    project proposed reference =
      proposed -
        (⟪reference, proposed⟫_ℝ / ‖reference‖ ^ 2) • reference := by
  simp [project, not_le.mpr hconflict]

/-- A conflicting direction forces the reference gradient to be nonzero. -/
theorem reference_ne_zero_of_conflict
    (proposed reference : Parameter)
    (hconflict : ⟪reference, proposed⟫_ℝ < 0) :
    reference ≠ 0 := by
  intro hzero
  subst reference
  simp at hconflict

/-- In the conflicting branch the projected direction lies exactly on the
half-space boundary. -/
theorem inner_project_of_conflict_eq_zero
    (proposed reference : Parameter)
    (hconflict : ⟪reference, proposed⟫_ℝ < 0) :
    ⟪reference, project proposed reference⟫_ℝ = 0 := by
  rw [project_of_conflict proposed reference hconflict]
  have hreference : ‖reference‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (reference_ne_zero_of_conflict proposed reference hconflict))
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  exact sub_eq_zero.mpr
    (div_mul_cancel₀ ⟪reference, proposed⟫_ℝ hreference).symm

/-- The closed form always satisfies the averaged replay constraint. -/
theorem project_feasible
    (proposed reference : Parameter) :
    Feasible reference (project proposed reference) := by
  by_cases hfeasible : Feasible reference proposed
  · rw [project_of_feasible proposed reference hfeasible]
    exact hfeasible
  · have hconflict : ⟪reference, proposed⟫_ℝ < 0 :=
      lt_of_not_ge hfeasible
    rw [Feasible, inner_project_of_conflict_eq_zero
      proposed reference hconflict]

/-- Applying the same A-GEM projection twice changes nothing. -/
@[simp] theorem project_idempotent
    (proposed reference : Parameter) :
    project (project proposed reference) reference =
      project proposed reference :=
  project_of_feasible _ _ (project_feasible proposed reference)

/-- Variational inequality characterizing the Euclidean half-space
projection. -/
theorem project_variationalInequality
    (proposed reference candidate : Parameter)
    (hcandidate : Feasible reference candidate) :
    0 ≤ ⟪project proposed reference - proposed,
      candidate - project proposed reference⟫_ℝ := by
  unfold Feasible at hcandidate
  by_cases hfeasible : Feasible reference proposed
  · rw [project_of_feasible proposed reference hfeasible, sub_self,
      inner_zero_left]
  · have hconflict : ⟪reference, proposed⟫_ℝ < 0 :=
      lt_of_not_ge hfeasible
    have hboundary :=
      inner_project_of_conflict_eq_zero proposed reference hconflict
    rw [project_of_conflict proposed reference hconflict] at hboundary
    have hreference : 0 < ‖reference‖ ^ 2 := by
      have hreferenceNonzero :=
        reference_ne_zero_of_conflict proposed reference hconflict
      exact sq_pos_of_pos (norm_pos_iff.mpr hreferenceNonzero)
    rw [project_of_conflict proposed reference hconflict]
    have hchosenDifference :
        (proposed -
            (⟪reference, proposed⟫_ℝ / ‖reference‖ ^ 2) • reference) -
              proposed =
          (-⟪reference, proposed⟫_ℝ / ‖reference‖ ^ 2) • reference := by
      module
    rw [hchosenDifference, real_inner_smul_left]
    have hcandidateDifference :
        0 ≤ ⟪reference,
          candidate -
            (proposed -
              (⟪reference, proposed⟫_ℝ / ‖reference‖ ^ 2) •
                reference)⟫_ℝ := by
      rw [inner_sub_right, hboundary]
      simpa using hcandidate
    exact mul_nonneg (div_nonneg (neg_nonneg.mpr hconflict.le)
      hreference.le) hcandidateDifference

/-- The A-GEM formula is globally closest to the proposed gradient among all
directions satisfying the averaged replay constraint. -/
theorem project_minimumChange
    (proposed reference candidate : Parameter)
    (hcandidate : Feasible reference candidate) :
    ‖project proposed reference - proposed‖ ^ 2 ≤
      ‖candidate - proposed‖ ^ 2 := by
  let chosen := project proposed reference
  have hvariation :
      0 ≤ ⟪chosen - proposed, candidate - chosen⟫_ℝ :=
    project_variationalInequality proposed reference candidate hcandidate
  have hdecompose :
      candidate - proposed =
        (chosen - proposed) + (candidate - chosen) := by
    abel
  rw [hdecompose, norm_add_sq_real]
  nlinarith [sq_nonneg ‖candidate - chosen‖]

/-- The Euclidean minimum is unique. -/
theorem project_unique_minimum
    (proposed reference candidate : Parameter)
    (hcandidate : Feasible reference candidate)
    (hequal :
      ‖candidate - proposed‖ ^ 2 =
        ‖project proposed reference - proposed‖ ^ 2) :
    candidate = project proposed reference := by
  let chosen := project proposed reference
  have hvariation :
      0 ≤ ⟪chosen - proposed, candidate - chosen⟫_ℝ :=
    project_variationalInequality proposed reference candidate hcandidate
  have hdecompose :
      candidate - proposed =
        (chosen - proposed) + (candidate - chosen) := by
    abel
  rw [hdecompose, norm_add_sq_real] at hequal
  have hzero : ‖candidate - chosen‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖candidate - chosen‖]
  have : candidate - chosen = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  exact sub_eq_zero.mp this

/-! ## From first-order feasibility to finite replay retention -/

open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
open Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent

/-- A-GEM's first-order half-space controls the actual replay loss only when
the finite-step curvature remainder fits inside its alignment margin. -/
theorem replayLoss_nonincrease_of_directionalTrust
    {loss : Parameter → ℝ} {parameter reference proposed : Parameter}
    {curvature step : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter reference
        (project proposed reference) curvature)
    (hstep : 0 ≤ step)
    (htrust :
      step * curvature / 2 ≤
        ⟪reference, project proposed reference⟫_ℝ) :
    loss (parameter - step • project proposed reference) ≤
      loss parameter := by
  have hupper := certificate step hstep
  have hscaled := mul_le_mul_of_nonneg_left htrust hstep
  nlinarith

/-! ## Executable fixtures and boundary -/

theorem scalar_conflict_projects_to_boundary :
    project (2 : ℝ) (-1 : ℝ) = 0 := by
  norm_num [project, Real.norm_eq_abs]

theorem scalar_compatible_direction_is_unchanged :
    project (2 : ℝ) (1 : ℝ) = 2 := by
  norm_num [project]

/-- At a stationary replay point the first-order constraint is vacuous, and
a finite nonlinear step can increase replay loss. -/
theorem stationary_replay_gradient_does_not_prevent_finite_forgetting :
    Feasible (0 : ℝ) (project (1 : ℝ) 0) ∧
      (0 - project (1 : ℝ) 0) ^ 2 > (0 : ℝ) ^ 2 := by
  norm_num [Feasible, project]

#print axioms inner_project_of_conflict_eq_zero
#print axioms project_feasible
#print axioms project_idempotent
#print axioms project_minimumChange
#print axioms project_unique_minimum
#print axioms replayLoss_nonincrease_of_directionalTrust
#print axioms scalar_conflict_projects_to_boundary
#print axioms stationary_replay_gradient_does_not_prevent_finite_forgetting

end

end AveragedGradientProjection

end Mettapedia.MachineLearning.ContinualLearning
