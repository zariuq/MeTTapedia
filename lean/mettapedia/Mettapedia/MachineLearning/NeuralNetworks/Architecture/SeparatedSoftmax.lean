import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RoutingExpansion

/-!
# Separated-softmax normalization boundary

Separated Softmax for Incremental Learning computes the classification
probability of an example using only the masses in that example's task group.
This blocks cross-group normalization during training.  The same model is
nevertheless evaluated by a joint classifier, so group-local normalization
does not by itself calibrate scores between groups.

This file isolates that reusable algebra.  Positive mass outside the active
group contributes an exact log-normalization penalty to a joint
cross-entropy, whereas the separated loss is invariant to that mass.  The
final fixture records the essential negative boundary: two singleton groups
both have separated probability one while their joint probabilities differ.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

/-- Probability of a target class when normalization is restricted to its
task group. -/
noncomputable def separatedGroupProbability
    (targetMass groupMass : ℝ) : ℝ :=
  normalizedRouteWeight targetMass groupMass

/-- Probability of the same target under joint normalization with every
outside group. -/
noncomputable def jointGroupProbability
    (targetMass groupMass outsideMass : ℝ) : ℝ :=
  expandedRouteWeight targetMass groupMass outsideMass

/-- The separated and joint normalizations agree exactly when no outside mass
is present. -/
@[simp] theorem jointGroupProbability_zero_outside
    (targetMass groupMass : ℝ) :
    jointGroupProbability targetMass groupMass 0 =
      separatedGroupProbability targetMass groupMass :=
  expandedRouteWeight_zero_newMass targetMass groupMass

/-- Positive mass from another task group strictly suppresses the joint
probability of every positive target in the active group. -/
theorem jointGroupProbability_lt_separated
    {targetMass groupMass outsideMass : ℝ}
    (targetPositive : 0 < targetMass)
    (groupPositive : 0 < groupMass)
    (outsidePositive : 0 < outsideMass) :
    jointGroupProbability targetMass groupMass outsideMass <
      separatedGroupProbability targetMass groupMass :=
  expandedRouteWeight_strictly_decreases targetPositive groupPositive
    outsidePositive

/-- Joint normalization is separated normalization multiplied by the mass
fraction retained by the active group. -/
theorem jointGroupProbability_factorization
    {targetMass groupMass outsideMass : ℝ}
    (groupNonzero : groupMass ≠ 0)
    (totalNonzero : groupMass + outsideMass ≠ 0) :
    jointGroupProbability targetMass groupMass outsideMass =
      separatedGroupProbability targetMass groupMass *
        (groupMass / (groupMass + outsideMass)) := by
  simp only [jointGroupProbability, separatedGroupProbability,
    expandedRouteWeight, normalizedRouteWeight]
  field_simp [groupNonzero, totalNonzero]

/-- Negative log-likelihood under task-group-local normalization. -/
noncomputable def separatedGroupNLL
    (targetMass groupMass : ℝ) : ℝ :=
  -Real.log (separatedGroupProbability targetMass groupMass)

/-- Negative log-likelihood under joint old/new-group normalization. -/
noncomputable def jointGroupNLL
    (targetMass groupMass outsideMass : ℝ) : ℝ :=
  -Real.log (jointGroupProbability targetMass groupMass outsideMass)

/-- Exact cross-group normalization penalty for a positive target and positive
group masses. -/
theorem jointGroupNLL_sub_separated_eq_log_ratio
    {targetMass groupMass outsideMass : ℝ}
    (targetPositive : 0 < targetMass)
    (groupPositive : 0 < groupMass)
    (outsidePositive : 0 < outsideMass) :
    jointGroupNLL targetMass groupMass outsideMass -
        separatedGroupNLL targetMass groupMass =
      Real.log ((groupMass + outsideMass) / groupMass) := by
  have targetNonzero : targetMass ≠ 0 := ne_of_gt targetPositive
  have groupNonzero : groupMass ≠ 0 := ne_of_gt groupPositive
  have totalPositive : 0 < groupMass + outsideMass :=
    add_pos groupPositive outsidePositive
  have totalNonzero : groupMass + outsideMass ≠ 0 := ne_of_gt totalPositive
  simp only [jointGroupNLL, separatedGroupNLL, jointGroupProbability,
    separatedGroupProbability, expandedRouteWeight, normalizedRouteWeight,
    Real.log_div targetNonzero totalNonzero,
    Real.log_div targetNonzero groupNonzero,
    Real.log_div totalNonzero groupNonzero]
  ring

/-- Positive outside-group mass makes the joint loss strictly larger than the
separated loss. -/
theorem separatedGroupNLL_lt_joint
    {targetMass groupMass outsideMass : ℝ}
    (targetPositive : 0 < targetMass)
    (groupPositive : 0 < groupMass)
    (outsidePositive : 0 < outsideMass) :
    separatedGroupNLL targetMass groupMass <
      jointGroupNLL targetMass groupMass outsideMass := by
  have ratioGreater :
      1 < (groupMass + outsideMass) / groupMass := by
    rw [lt_div_iff₀ groupPositive]
    nlinarith
  have logRatioPositive :
      0 < Real.log ((groupMass + outsideMass) / groupMass) :=
    Real.log_pos ratioGreater
  have exactPenalty :=
    jointGroupNLL_sub_separated_eq_log_ratio targetPositive groupPositive
      outsidePositive
  linarith

/-- A finite outside-group logit always adds positive softmax mass and hence a
strict joint-normalization penalty. -/
theorem finiteOutsideLogit_penalizes_jointProbability
    (targetLogit outsideLogit groupMass : ℝ)
    (groupPositive : 0 < groupMass) :
    jointGroupProbability (Real.exp targetLogit) groupMass
        (Real.exp outsideLogit) <
      separatedGroupProbability (Real.exp targetLogit) groupMass :=
  jointGroupProbability_lt_separated (Real.exp_pos targetLogit)
    groupPositive (Real.exp_pos outsideLogit)

/-- Negative boundary: group-local normalization does not calibrate groups for
the joint classifier.  Each singleton group assigns its own target probability
one, while the joint classifier prefers the group with twice the mass. -/
theorem singleton_separated_probabilities_do_not_calibrate_joint :
    separatedGroupProbability 1 1 = 1 ∧
      separatedGroupProbability 2 2 = 1 ∧
      jointGroupProbability 1 1 2 = (1 / 3 : ℝ) ∧
      jointGroupProbability 2 2 1 = (2 / 3 : ℝ) := by
  norm_num [separatedGroupProbability, jointGroupProbability,
    normalizedRouteWeight, expandedRouteWeight]

#print axioms jointGroupProbability_zero_outside
#print axioms jointGroupProbability_lt_separated
#print axioms jointGroupProbability_factorization
#print axioms jointGroupNLL_sub_separated_eq_log_ratio
#print axioms separatedGroupNLL_lt_joint
#print axioms finiteOutsideLogit_penalizes_jointProbability
#print axioms singleton_separated_probabilities_do_not_calibrate_joint

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
