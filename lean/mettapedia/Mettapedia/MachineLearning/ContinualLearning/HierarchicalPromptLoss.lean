import Mathlib

/-!
# Hierarchical continual-learning loss decomposition

Wang et al., *Hierarchical Decomposition of Prompt-Based Continual Learning:
Rethinking Obscured Sub-optimality* (arXiv:2310.07234), decompose the
class-incremental probability of a correct class into within-task prediction
and task-identity inference (Equation 5).  They additionally retain a
task-adaptive all-class prediction loss and define the complete loss as the
maximum of the hierarchical and task-adaptive losses (Equations 6--8 and
Appendix A, Equations 13--19).

This file separates the probability identity from the loss-budget algebra.
Negative log loss turns the probability product into addition exactly.
Nonnegative upper bounds on within-task, task-identity, and task-adaptive loss
therefore give the source's maximum upper bound.  Conversely, a small complete
loss forces each component loss to be small.

The appendix replaces inequalities by equality when substituting declared
upper bounds.  That inference is not valid: a zero-loss fixture satisfies
strictly positive component budgets while the complete loss remains zero.
The checked result keeps the theorem statement's correct interval bound.

No claim is made about learned prompts, representation distributions,
Gaussian pseudo-features, optimization of the three heads, rehearsal freedom,
or empirical accuracy.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace HierarchicalPromptLoss

/-! ## Probability-to-loss decomposition -/

/-- One-hot cross-entropy for a correct event of probability `probability`. -/
noncomputable def negativeLogLoss (probability : ℝ) : ℝ :=
  -Real.log probability

/-- The hierarchical class loss is within-task loss plus task-identity loss. -/
def jointClassLoss
    (withinTask taskIdentity : ℝ) : ℝ :=
  withinTask + taskIdentity

/-- The source's complete loss is the worse of the hierarchical class loss
and the task-adaptive all-class loss. -/
def hierarchicalLoss
    (withinTask taskIdentity taskAdaptive : ℝ) : ℝ :=
  max (jointClassLoss withinTask taskIdentity) taskAdaptive

/-- Equation 5 under negative log loss: multiplying the within-task and
task-identity probabilities adds their one-hot cross-entropies. -/
theorem negativeLogLoss_mul
    {withinProbability taskProbability : ℝ}
    (within_nonzero : withinProbability ≠ 0)
    (task_nonzero : taskProbability ≠ 0) :
    negativeLogLoss (withinProbability * taskProbability) =
      jointClassLoss
        (negativeLogLoss withinProbability)
        (negativeLogLoss taskProbability) := by
  unfold negativeLogLoss jointClassLoss
  rw [Real.log_mul within_nonzero task_nonzero]
  ring

/-- Correct-event negative log loss is nonnegative for a probability in
`(0, 1]`. -/
theorem negativeLogLoss_nonnegative
    {probability : ℝ}
    (positive : 0 < probability)
    (at_most_one : probability ≤ 1) :
    0 ≤ negativeLogLoss probability := by
  dsimp [negativeLogLoss]
  linarith [Real.log_nonpos positive.le at_most_one]

/-! ## Exact component-budget boundary -/

/-- Source Theorem 1, expressed at the loss level.  The result is an upper
bound, not equality with the declared budgets. -/
theorem hierarchicalLoss_mem_Icc_of_component_bounds
    {withinTask taskIdentity taskAdaptive δ ε η : ℝ}
    (within_nonnegative : 0 ≤ withinTask)
    (task_nonnegative : 0 ≤ taskIdentity)
    (within_bound : withinTask ≤ δ)
    (task_bound : taskIdentity ≤ ε)
    (adaptive_bound : taskAdaptive ≤ η) :
    hierarchicalLoss withinTask taskIdentity taskAdaptive ∈
      Set.Icc 0 (max (δ + ε) η) := by
  constructor
  · exact
      le_trans
        (add_nonneg within_nonnegative task_nonnegative)
        (le_max_left _ _)
  · apply max_le
    · exact
        (show jointClassLoss withinTask taskIdentity ≤ δ + ε by
          simpa [jointClassLoss] using
            add_le_add within_bound task_bound).trans
          (le_max_left _ _)
    · exact adaptive_bound.trans (le_max_right _ _)

/-- Source Theorem 2's necessary direction: a small complete loss forces
each nonnegative component to fit the same budget. -/
theorem componentLosses_le_of_hierarchicalLoss_le
    {withinTask taskIdentity taskAdaptive ξ : ℝ}
    (within_nonnegative : 0 ≤ withinTask)
    (task_nonnegative : 0 ≤ taskIdentity)
    (complete_bound :
      hierarchicalLoss withinTask taskIdentity taskAdaptive ≤ ξ) :
    withinTask ≤ ξ ∧ taskIdentity ≤ ξ ∧ taskAdaptive ≤ ξ := by
  have joint_bound :
      jointClassLoss withinTask taskIdentity ≤ ξ :=
    (le_max_left
      (jointClassLoss withinTask taskIdentity) taskAdaptive).trans
      complete_bound
  have adaptive_bound :
      taskAdaptive ≤ ξ :=
    (le_max_right
      (jointClassLoss withinTask taskIdentity) taskAdaptive).trans
      complete_bound
  constructor
  · exact
      (le_add_of_nonneg_right task_nonnegative).trans joint_bound
  · constructor
    · exact
        (le_add_of_nonneg_left within_nonnegative).trans joint_bound
    · exact adaptive_bound

/-- Tight component budgets recover the exact source upper envelope. -/
theorem hierarchicalLoss_le_max_componentBudgets
    {withinTask taskIdentity taskAdaptive δ ε η : ℝ}
    (within_bound : withinTask ≤ δ)
    (task_bound : taskIdentity ≤ ε)
    (adaptive_bound : taskAdaptive ≤ η) :
    hierarchicalLoss withinTask taskIdentity taskAdaptive ≤
      max (δ + ε) η := by
  apply max_le
  · exact
      (show jointClassLoss withinTask taskIdentity ≤ δ + ε by
        simpa [jointClassLoss] using
          add_le_add within_bound task_bound).trans
        (le_max_left _ _)
  · exact adaptive_bound.trans (le_max_right _ _)

/-! ## Boundaries and executable fixtures -/

/-- Upper bounds do not become exact loss values.  This refutes the equality
substitution in Appendix A while satisfying the theorem's interval bound. -/
theorem component_upper_bounds_do_not_force_envelope_equality :
    hierarchicalLoss 0 0 0 = 0 ∧
      max ((1 : ℝ) + 1) 1 = 2 ∧
      hierarchicalLoss 0 0 0 ≠ max ((1 : ℝ) + 1) 1 := by
  norm_num [hierarchicalLoss, jointClassLoss]

/-- The same joint correct-class probability can hide different allocations
between within-task prediction and task-identity inference. -/
theorem equal_joint_probability_different_components :
    ((1 : ℝ) / 2) * ((1 : ℝ) / 2) =
        ((1 : ℝ) / 4) * 1 ∧
      ((1 : ℝ) / 2) ≠ (1 : ℝ) / 4 ∧
      ((1 : ℝ) / 2) ≠ 1 := by
  norm_num

/-- Improving one probability strictly improves the product only when the
other hierarchical probability is strictly positive. -/
theorem jointProbability_strictMono_within
    {withinOld withinNew taskProbability : ℝ}
    (improves : withinOld < withinNew)
    (task_positive : 0 < taskProbability) :
    withinOld * taskProbability <
      withinNew * taskProbability :=
  mul_lt_mul_of_pos_right improves task_positive

/-- At zero task probability, a strict within-task improvement is invisible
to the joint probability. -/
theorem zero_task_probability_masks_within_improvement :
    ((0 : ℝ) < 1) ∧
      (0 : ℝ) * 0 = 1 * 0 := by
  norm_num

end HierarchicalPromptLoss

end Mettapedia.MachineLearning.ContinualLearning
