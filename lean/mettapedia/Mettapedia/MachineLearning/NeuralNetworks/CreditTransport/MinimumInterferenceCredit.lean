import Mettapedia.MachineLearning.ContinualLearning.AveragedGradientProjection
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MetricDependentSteepestDescent

/-!
# Minimum-interference credit and its conditional advantage boundary

Backpropagation is the Euclidean steepest first-order descent direction for
the current loss.  A different credit can therefore be strictly preferable
only after the objective changes.  This file studies the simplest such
change: retain performance measured by a replay gradient while learning the
current example.

The minimum-interference direction is the Euclidean projection of the current
gradient onto the replay half-space.  In the conflicting branch it sacrifices
a known amount of current-loss margin, removes the replay interference
exactly, and beats raw backpropagation for a retention-weighted first-order
score exactly when the retention weight exceeds an explicit observable
threshold.  Compatible gradients give a negative boundary example: the
projection is exactly backpropagation and no strict advantage is possible.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace MinimumInterferenceCredit

noncomputable section

open scoped InnerProductSpace
open Mettapedia.MachineLearning.ContinualLearning

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- The closest replay-feasible direction to the current gradient. -/
def direction (current replay : Parameter) : Parameter :=
  AveragedGradientProjection.project current replay

/-- First-order utility combining current-loss decrease and replay-loss
decrease with an explicit retention weight. -/
def retentionWeightedScore
    (current replay : Parameter) (retentionWeight : ℝ)
    (candidate : Parameter) : ℝ :=
  ⟪current, candidate⟫_ℝ +
    retentionWeight * ⟪replay, candidate⟫_ℝ

/-- The minimum-interference direction always satisfies the replay
first-order non-interference constraint. -/
theorem direction_feasible (current replay : Parameter) :
    AveragedGradientProjection.Feasible replay (direction current replay) :=
  AveragedGradientProjection.project_feasible current replay

/-- When current and replay gradients are compatible, the construction is
exactly backpropagation. -/
@[simp] theorem direction_eq_current_of_compatible
    (current replay : Parameter)
    (compatible : 0 ≤ ⟪replay, current⟫_ℝ) :
    direction current replay = current := by
  exact AveragedGradientProjection.project_of_feasible current replay compatible

/-- Under conflict, the direction is the usual one-half-space projection. -/
theorem direction_eq_sub_projection_of_conflict
    (current replay : Parameter)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    direction current replay =
      current -
        (⟪replay, current⟫_ℝ / ‖replay‖ ^ 2) • replay :=
  AveragedGradientProjection.project_of_conflict current replay conflict

/-- Under conflict, replay interference is removed exactly. -/
theorem replay_margin_eq_zero_of_conflict
    (current replay : Parameter)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    ⟪replay, direction current replay⟫_ℝ = 0 :=
  AveragedGradientProjection.inner_project_of_conflict_eq_zero
    current replay conflict

/-- The construction is globally closest to the current gradient among all
replay-feasible directions. -/
theorem direction_minimum_change
    (current replay candidate : Parameter)
    (candidate_feasible :
      AveragedGradientProjection.Feasible replay candidate) :
    ‖direction current replay - current‖ ^ 2 ≤
      ‖candidate - current‖ ^ 2 :=
  AveragedGradientProjection.project_minimumChange
    current replay candidate candidate_feasible

/-- The exact current-loss margin left after removing replay interference. -/
theorem current_margin_eq_of_conflict
    (current replay : Parameter)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    ⟪current, direction current replay⟫_ℝ =
      ‖current‖ ^ 2 -
        ⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 := by
  rw [direction_eq_sub_projection_of_conflict current replay conflict,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm replay current]
  ring

/-- Resolving a genuine conflict strictly reduces current-loss first-order
margin compared with raw backpropagation.  This is the unavoidable price of
retention, not a free current-task improvement. -/
theorem current_margin_lt_bp_of_conflict
    (current replay : Parameter)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    ⟪current, direction current replay⟫_ℝ < ‖current‖ ^ 2 := by
  rw [current_margin_eq_of_conflict current replay conflict]
  have replay_ne_zero : replay ≠ 0 :=
    AveragedGradientProjection.reference_ne_zero_of_conflict
      current replay conflict
  have replay_norm_sq_pos : 0 < ‖replay‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr replay_ne_zero)
  have conflict_sq_pos : 0 < ⟪replay, current⟫_ℝ ^ 2 :=
    sq_pos_of_neg conflict
  have : 0 < ⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 :=
    div_pos conflict_sq_pos replay_norm_sq_pos
  linarith

/-- Exact score of the minimum-interference direction in the conflicting
branch.  Its replay term vanishes, leaving the current margin minus the
projection cost. -/
theorem retentionWeightedScore_direction_eq_of_conflict
    (current replay : Parameter) (retentionWeight : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay retentionWeight
        (direction current replay) =
      ‖current‖ ^ 2 -
        ⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 := by
  rw [retentionWeightedScore, current_margin_eq_of_conflict current replay conflict,
    replay_margin_eq_zero_of_conflict current replay conflict]
  ring

/-- Raw backpropagation's retention-weighted first-order score. -/
theorem retentionWeightedScore_current
    (current replay : Parameter) (retentionWeight : ℝ) :
    retentionWeightedScore current replay retentionWeight current =
      ‖current‖ ^ 2 +
        retentionWeight * ⟪replay, current⟫_ℝ := by
  rw [retentionWeightedScore, real_inner_self_eq_norm_sq]

/-- **Exact conditional-advantage boundary.**  Under genuine gradient
conflict, the minimum-interference direction beats raw backpropagation for the
retention-weighted first-order score exactly when the weighted replay value
exceeds the interference correction: `-⟪replay,current⟫ < weight * ‖replay‖²`.
Every quantity is observable from the two credit vectors. -/
theorem direction_score_gt_bp_iff
    (current replay : Parameter) (retentionWeight : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay retentionWeight
        (direction current replay) >
      retentionWeightedScore current replay retentionWeight current ↔
    -⟪replay, current⟫_ℝ < retentionWeight * ‖replay‖ ^ 2 := by
  rw [retentionWeightedScore_direction_eq_of_conflict
      current replay retentionWeight conflict,
    retentionWeightedScore_current]
  have replay_ne_zero : replay ≠ 0 :=
    AveragedGradientProjection.reference_ne_zero_of_conflict
      current replay conflict
  have replay_norm_sq_pos : 0 < ‖replay‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr replay_ne_zero)
  constructor <;> intro h
  · have hscaled := (div_lt_iff₀ replay_norm_sq_pos).mp
      (show ⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 <
          -retentionWeight * ⟪replay, current⟫_ℝ by linarith)
    nlinarith
  · have hscaled :
        ⟪replay, current⟫_ℝ ^ 2 <
          -retentionWeight * ⟪replay, current⟫_ℝ * ‖replay‖ ^ 2 := by
      nlinarith
    have hdiv := (div_lt_iff₀ replay_norm_sq_pos).mpr
      (show ⟪replay, current⟫_ℝ ^ 2 <
          (-retentionWeight * ⟪replay, current⟫_ℝ) * ‖replay‖ ^ 2 by
        simpa [mul_assoc] using hscaled)
    linarith

/-- At the exact threshold the two directions have equal combined score. -/
theorem direction_score_eq_bp_iff
    (current replay : Parameter) (retentionWeight : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay retentionWeight
        (direction current replay) =
      retentionWeightedScore current replay retentionWeight current ↔
    -⟪replay, current⟫_ℝ = retentionWeight * ‖replay‖ ^ 2 := by
  rw [retentionWeightedScore_direction_eq_of_conflict
      current replay retentionWeight conflict,
    retentionWeightedScore_current]
  have replay_ne_zero : replay ≠ 0 :=
    AveragedGradientProjection.reference_ne_zero_of_conflict
      current replay conflict
  have replay_norm_sq_ne : ‖replay‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr replay_ne_zero))
  field_simp [replay_norm_sq_ne]
  constructor <;> intro h <;> nlinarith

/-- Below the same threshold, raw backpropagation has the larger combined
score.  Together with the preceding two theorems, this gives the complete
three-way boundary. -/
theorem direction_score_lt_bp_iff
    (current replay : Parameter) (retentionWeight : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay retentionWeight
        (direction current replay) <
      retentionWeightedScore current replay retentionWeight current ↔
    retentionWeight * ‖replay‖ ^ 2 < -⟪replay, current⟫_ℝ := by
  constructor
  · intro score_lt
    by_contra threshold_not_lt
    have threshold_le :
        -⟪replay, current⟫_ℝ ≤ retentionWeight * ‖replay‖ ^ 2 :=
      le_of_not_gt threshold_not_lt
    rcases threshold_le.eq_or_lt with threshold_eq | threshold_lt
    · have score_eq := (direction_score_eq_bp_iff current replay
          retentionWeight conflict).2 threshold_eq
      linarith
    · have score_gt := (direction_score_gt_bp_iff current replay
          retentionWeight conflict).2 threshold_lt
      linarith
  · intro threshold_lt
    by_contra score_not_lt
    have score_le :
        retentionWeightedScore current replay retentionWeight current ≤
          retentionWeightedScore current replay retentionWeight
            (direction current replay) :=
      le_of_not_gt score_not_lt
    rcases score_le.eq_or_lt with score_eq | score_lt
    · have threshold_eq := (direction_score_eq_bp_iff current replay
          retentionWeight conflict).1 score_eq.symm
      linarith
    · have threshold_gt := (direction_score_gt_bp_iff current replay
          retentionWeight conflict).1 score_lt
      linarith

/-- If retention carries zero value, projecting away current-task conflict is
strictly worse than raw BP.  Constraint information only helps after the
objective assigns it a positive, sufficiently large exchange rate. -/
theorem direction_score_lt_bp_of_zero_retentionWeight
    (current replay : Parameter) (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay 0 (direction current replay) <
      retentionWeightedScore current replay 0 current := by
  apply (direction_score_lt_bp_iff current replay 0 conflict).2
  simpa using (neg_pos.mpr conflict)

/-- Compatible gradients form the no-advantage boundary: the construction is
BP itself and therefore has exactly the same score for every retention
weight. -/
theorem compatible_score_eq_bp
    (current replay : Parameter) (retentionWeight : ℝ)
    (compatible : 0 ≤ ⟪replay, current⟫_ℝ) :
    retentionWeightedScore current replay retentionWeight
        (direction current replay) =
      retentionWeightedScore current replay retentionWeight current := by
  rw [direction_eq_current_of_compatible current replay compatible]

/-! ## Positive, threshold, and negative examples -/

namespace PlaneWitness

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def plane (first second : ℝ) : Plane :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![first, second]

noncomputable def current : Plane := plane 1 (-1)

noncomputable def replay : Plane := plane 0 1

theorem replay_inner_current : ⟪replay, current⟫_ℝ = -1 := by
  norm_num [replay, current, plane, WithLp.equiv, PiLp.inner_apply,
    Fin.sum_univ_two]

theorem conflict : ⟪replay, current⟫_ℝ < 0 := by
  rw [replay_inner_current]
  norm_num

private theorem plane_norm_sq (vector : Plane) :
    ‖vector‖ ^ 2 = vector 0 ^ 2 + vector 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem replay_norm_sq : ‖replay‖ ^ 2 = 1 := by
  rw [plane_norm_sq]
  norm_num [replay, plane, WithLp.equiv]

theorem current_norm_sq : ‖current‖ ^ 2 = 2 := by
  rw [plane_norm_sq]
  norm_num [current, plane, WithLp.equiv]

theorem positive_advantage :
    retentionWeightedScore current replay 2 (direction current replay) >
      retentionWeightedScore current replay 2 current := by
  rw [direction_score_gt_bp_iff current replay 2 conflict, replay_norm_sq]
  rw [replay_inner_current]
  norm_num

theorem threshold_tie :
    retentionWeightedScore current replay 1 (direction current replay) =
      retentionWeightedScore current replay 1 current := by
  rw [direction_score_eq_bp_iff current replay 1 conflict, replay_norm_sq]
  rw [replay_inner_current]
  norm_num

theorem below_threshold_bp_wins :
    retentionWeightedScore current replay (1 / 2)
        (direction current replay) <
      retentionWeightedScore current replay (1 / 2) current := by
  rw [retentionWeightedScore_direction_eq_of_conflict current replay
      (1 / 2) conflict,
    retentionWeightedScore_current, replay_norm_sq, current_norm_sq,
    replay_inner_current]
  norm_num

end PlaneWitness

namespace CompatibleWitness

theorem no_strict_advantage :
    ¬ retentionWeightedScore (1 : ℝ) 1 7 (direction 1 1) >
      retentionWeightedScore (1 : ℝ) 1 7 1 := by
  rw [compatible_score_eq_bp (1 : ℝ) 1 7 (by norm_num)]
  exact lt_irrefl _

end CompatibleWitness

#print axioms direction_minimum_change
#print axioms current_margin_lt_bp_of_conflict
#print axioms direction_score_gt_bp_iff
#print axioms direction_score_eq_bp_iff
#print axioms direction_score_lt_bp_iff
#print axioms direction_score_lt_bp_of_zero_retentionWeight
#print axioms PlaneWitness.positive_advantage
#print axioms PlaneWitness.threshold_tie
#print axioms PlaneWitness.below_threshold_bp_wins
#print axioms CompatibleWitness.no_strict_advantage

end

end MinimumInterferenceCredit

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
