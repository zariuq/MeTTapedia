import Mathlib

/-!
# Hypernetwork output retention

von Oswald, Henning, Sacramento, and Grewe,
*Continual Learning with Hypernetworks*
(ICLR 2020, arXiv:1906.00695), Equation (2), regularize the generated target
weights at saved task embeddings rather than replaying every old task datum.

This file isolates the exact finite core of that construction.  The sum of
squared generated-weight drifts is zero exactly when every registered old-task
weight is unchanged.  A single task's drift is bounded by the square root of
the aggregate penalty, and any declared Lipschitz target readout transports
that bound to output drift.

Two boundaries remain explicit:

* zero penalty on a sampled subset says nothing about an unsampled old task;
* unchanged hypernetwork parameters do not preserve a task's generated weight
  if its saved embedding is itself changed.

The `after` map can include the source's proposed look-ahead parameter change.
No theorem claims that minimizing a finite-weight regularizer reaches zero,
that a target network is globally Lipschitz, or that task identity is known at
test time.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace HypernetworkOutputRetention

noncomputable section

variable {Task Weight Input Output : Type*}

section Penalty

variable [NormedAddCommGroup Weight]

/-- Sum of squared generated-weight drift over registered old tasks.  The
source's positive scale and averaging factor do not change its zero set. -/
def outputRetentionPenalty
    (registered : Finset Task)
    (before after : Task → Weight) : ℝ :=
  ∑ task ∈ registered, ‖before task - after task‖ ^ 2

theorem outputRetentionPenalty_nonnegative
    (registered : Finset Task)
    (before after : Task → Weight) :
    0 ≤ outputRetentionPenalty registered before after := by
  unfold outputRetentionPenalty
  exact Finset.sum_nonneg fun task _ =>
    sq_nonneg ‖before task - after task‖

/-- Every registered task's squared drift is bounded by the aggregate
retention penalty. -/
theorem task_drift_sq_le_penalty
    (registered : Finset Task)
    (before after : Task → Weight)
    {task : Task}
    (task_registered : task ∈ registered) :
    ‖before task - after task‖ ^ 2 ≤
      outputRetentionPenalty registered before after := by
  unfold outputRetentionPenalty
  exact Finset.single_le_sum
    (fun index _ => sq_nonneg ‖before index - after index‖)
    task_registered

/-- A zero aggregate penalty is equivalent to exact generated-weight retention
for every registered task. -/
theorem outputRetentionPenalty_eq_zero_iff
    (registered : Finset Task)
    (before after : Task → Weight) :
    outputRetentionPenalty registered before after = 0 ↔
      ∀ task ∈ registered, before task = after task := by
  unfold outputRetentionPenalty
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro zero task task_registered
      have task_zero := zero task task_registered
      have norm_zero :
          ‖before task - after task‖ = 0 :=
        (sq_eq_zero_iff).mp task_zero
      exact sub_eq_zero.mp (norm_eq_zero.mp norm_zero)
    · intro equal task task_registered
      simp [equal task task_registered]
  · intro task _
    exact sq_nonneg ‖before task - after task‖

/-- A positive regularization scale preserves exactly the same zero set. -/
theorem scaled_outputRetentionPenalty_eq_zero_iff
    (registered : Finset Task)
    (before after : Task → Weight)
    {scale : ℝ}
    (scale_positive : 0 < scale) :
    scale * outputRetentionPenalty registered before after = 0 ↔
      ∀ task ∈ registered, before task = after task := by
  rw [mul_eq_zero]
  simp only [ne_of_gt scale_positive, false_or]
  exact outputRetentionPenalty_eq_zero_iff registered before after

/-- Exact generated-weight retention preserves any deterministic target
readout applied to those weights. -/
theorem target_behavior_preserved_of_zero_penalty
    (registered : Finset Task)
    (before after : Task → Weight)
    (predict : Weight → Input → Output)
    (input : Input)
    {task : Task}
    (task_registered : task ∈ registered)
    (zero :
      outputRetentionPenalty registered before after = 0) :
    predict (before task) input = predict (after task) input := by
  have retained :=
    (outputRetentionPenalty_eq_zero_iff registered before after).mp
      zero task task_registered
  rw [retained]

/-- The aggregate penalty gives a pointwise generated-weight drift bound. -/
theorem task_drift_le_sqrt_penalty
    (registered : Finset Task)
    (before after : Task → Weight)
    {task : Task}
    (task_registered : task ∈ registered) :
    ‖before task - after task‖ ≤
      Real.sqrt (outputRetentionPenalty registered before after) := by
  rw [Real.le_sqrt
    (norm_nonneg (before task - after task))
    (outputRetentionPenalty_nonnegative registered before after)]
  exact task_drift_sq_le_penalty
    registered before after task_registered

section LipschitzReadout

variable [NormedAddCommGroup Output]

/-- A declared pointwise Lipschitz readout transports the generated-weight
penalty into a target-output drift bound. -/
theorem target_output_drift_le_sqrt_penalty
    (registered : Finset Task)
    (before after : Task → Weight)
    (predict : Weight → Input → Output)
    (input : Input)
    {task : Task}
    (task_registered : task ∈ registered)
    {lipschitz : ℝ}
    (lipschitz_nonnegative : 0 ≤ lipschitz)
    (readout_bound :
      ∀ first second,
        ‖predict first input - predict second input‖ ≤
          lipschitz * ‖first - second‖) :
    ‖predict (before task) input - predict (after task) input‖ ≤
      lipschitz *
        Real.sqrt (outputRetentionPenalty registered before after) := by
  calc
    ‖predict (before task) input - predict (after task) input‖
        ≤ lipschitz * ‖before task - after task‖ :=
      readout_bound (before task) (after task)
    _ ≤ lipschitz *
        Real.sqrt (outputRetentionPenalty registered before after) :=
      mul_le_mul_of_nonneg_left
        (task_drift_le_sqrt_penalty
          registered before after task_registered)
        lipschitz_nonnegative

end LipschitzReadout

end Penalty

/-! ## Executable boundaries -/

/-- One registered task is retained while an omitted task changes. -/
def sampledBefore : Bool → ℝ := fun _ => 0

def sampledAfter : Bool → ℝ
  | false => 0
  | true => 1

/-- Negative boundary: a zero penalty on a sampled subset does not protect an
unsampled old task. -/
theorem sampled_subset_zero_does_not_protect_omitted_task :
    outputRetentionPenalty {false} sampledBefore sampledAfter = 0 ∧
      sampledBefore true ≠ sampledAfter true := by
  norm_num
    [outputRetentionPenalty, sampledBefore, sampledAfter, Real.norm_eq_abs]

/-- A scalar hypernetwork sufficient to expose the saved-embedding boundary. -/
def scalarHypernetwork
    (embedding parameter : ℝ) : ℝ :=
  embedding + parameter

/-- Negative boundary: keeping the hypernetwork parameter fixed is not enough
if an old task embedding is allowed to move. -/
theorem fixed_parameter_changed_embedding_changes_generated_weight :
    scalarHypernetwork 0 3 ≠ scalarHypernetwork 1 3 := by
  norm_num [scalarHypernetwork]

/-- Positive fixture: two exact drifts of three and four have aggregate
squared penalty twenty-five. -/
def twoTaskAfter : Bool → ℝ
  | false => 3
  | true => 4

theorem twoTask_three_four_penalty :
    outputRetentionPenalty Finset.univ sampledBefore twoTaskAfter = 25 := by
  norm_num
    [outputRetentionPenalty, sampledBefore, twoTaskAfter, Real.norm_eq_abs]

end

end HypernetworkOutputRetention

end Mettapedia.MachineLearning.ContinualLearning

#print axioms Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention.outputRetentionPenalty_eq_zero_iff
#print axioms Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention.target_behavior_preserved_of_zero_penalty
#print axioms Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention.target_output_drift_le_sqrt_penalty
#print axioms Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention.sampled_subset_zero_does_not_protect_omitted_task
#print axioms Mettapedia.MachineLearning.ContinualLearning.HypernetworkOutputRetention.fixed_parameter_changed_embedding_changes_generated_weight
