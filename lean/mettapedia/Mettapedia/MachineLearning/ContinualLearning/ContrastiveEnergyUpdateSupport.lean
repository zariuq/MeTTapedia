import Mathlib

/-!
# Update support of contrastive energy learning

Li, Du, van de Ven, and Mordatch, *Energy-Based Models for Continual
Learning* (arXiv:2011.12216), contrast the normalized maximum-likelihood
objective in their Equation (4) with the sampled positive/negative energy
difference in Equation (5).

This file isolates that distinction in a finite tabular energy chart.  It
proves:

* a normalized energy-gradient step changes every non-target label because
  every finite Boltzmann mass is positive;
* a sampled pairwise step changes only the positive and negative labels;
* the source condition that the negative label differs from the positive
  label is load bearing;
* a three-label fixture strictly separates the two update supports.

The tabular result does not imply that a shared neural parameter affects only
two labels: parameter sharing can transport either local energy-coordinate
update through the common network.  It also does not prove the source's
empirical forgetting or accuracy results.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ContrastiveEnergyUpdateSupport

open scoped BigOperators

noncomputable section

variable {Label : Type*}

section Normalized

variable [Fintype Label] [DecidableEq Label]

/-- Finite Boltzmann partition for one input and a table of label energies. -/
def energyPartition (energy : Label → ℝ) : ℝ :=
  ∑ label, Real.exp (-energy label)

/-- Conditional probability induced by the finite energy table. -/
def energyProbability (energy : Label → ℝ) (label : Label) : ℝ :=
  Real.exp (-energy label) / energyPartition energy

omit [DecidableEq Label] in
theorem energyPartition_pos [Nonempty Label]
    (energy : Label → ℝ) :
    0 < energyPartition energy := by
  apply Finset.sum_pos
  · intro label _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

omit [DecidableEq Label] in
theorem energyProbability_pos [Nonempty Label]
    (energy : Label → ℝ) (label : Label) :
    0 < energyProbability energy label :=
  div_pos (Real.exp_pos _) (energyPartition_pos energy)

omit [DecidableEq Label] in
theorem sum_energyProbability_eq_one [Nonempty Label]
    (energy : Label → ℝ) :
    ∑ label, energyProbability energy label = 1 := by
  simp only [energyProbability, ← Finset.sum_div, energyPartition]
  exact div_self (ne_of_gt (energyPartition_pos energy))

/-- Energy-coordinate gradient of normalized negative log-likelihood:
`1 - p(target)` at the target and `-p(label)` elsewhere. -/
def normalizedEnergyGradient
    (energy : Label → ℝ) (target label : Label) : ℝ :=
  (if label = target then 1 else 0) -
    energyProbability energy label

/-- One gradient-descent step for the normalized energy objective. -/
def normalizedEnergyStep
    (rate : ℝ) (energy : Label → ℝ) (target : Label) : Label → ℝ :=
  fun label =>
    energy label -
      rate * normalizedEnergyGradient energy target label

/-- Every non-target label receives a strict energy increase under a positive
normalized-likelihood step. -/
theorem normalizedEnergyStep_strictly_changes_nonTarget
    [Nonempty Label]
    {rate : ℝ} (rate_pos : 0 < rate)
    (energy : Label → ℝ) (target : Label)
    {label : Label} (label_ne : label ≠ target) :
    energy label < normalizedEnergyStep rate energy target label := by
  have probability_pos := energyProbability_pos energy label
  simp only [normalizedEnergyStep, normalizedEnergyGradient,
    if_neg label_ne]
  nlinarith

end Normalized

section Pairwise

variable [DecidableEq Label]

/-- Sampled contrastive loss from Equation (5), for one positive and one
negative label. -/
def pairwiseContrastiveLoss
    (energy : Label → ℝ) (positive negative : Label) : ℝ :=
  energy positive - energy negative

/-- Exact coordinate gradient of the sampled pairwise loss. -/
def pairwiseContrastiveGradient
    (positive negative label : Label) : ℝ :=
  (if label = positive then 1 else 0) -
    (if label = negative then 1 else 0)

/-- One gradient-descent step for the sampled pairwise objective. -/
def pairwiseContrastiveStep
    (rate : ℝ) (energy : Label → ℝ)
    (positive negative : Label) : Label → ℝ :=
  fun label =>
    energy label -
      rate * pairwiseContrastiveGradient positive negative label

/-- Every energy coordinate outside the sampled positive/negative pair is
unchanged exactly. -/
theorem pairwiseContrastiveStep_eq_of_outside
    (rate : ℝ) (energy : Label → ℝ)
    (positive negative label : Label)
    (label_ne_positive : label ≠ positive)
    (label_ne_negative : label ≠ negative) :
    pairwiseContrastiveStep rate energy positive negative label =
      energy label := by
  simp [pairwiseContrastiveStep, pairwiseContrastiveGradient,
    label_ne_positive, label_ne_negative]

/-- Conversely, a changed coordinate must be one of the sampled labels. -/
theorem pairwiseContrastiveStep_changed_only_at_pair
    (rate : ℝ) (energy : Label → ℝ)
    (positive negative label : Label)
    (changed :
      pairwiseContrastiveStep rate energy positive negative label ≠
        energy label) :
    label = positive ∨ label = negative := by
  by_contra outside
  push Not at outside
  exact changed
    (pairwiseContrastiveStep_eq_of_outside
      rate energy positive negative label outside.1 outside.2)

/-- With distinct labels, descent lowers the positive energy by exactly the
learning rate. -/
theorem pairwiseContrastiveStep_positive
    (rate : ℝ) (energy : Label → ℝ)
    {positive negative : Label}
    (distinct : positive ≠ negative) :
    pairwiseContrastiveStep rate energy positive negative positive =
      energy positive - rate := by
  simp [pairwiseContrastiveStep, pairwiseContrastiveGradient, distinct]

/-- With distinct labels, descent raises the sampled negative energy by
exactly the learning rate. -/
theorem pairwiseContrastiveStep_negative
    (rate : ℝ) (energy : Label → ℝ)
    {positive negative : Label}
    (distinct : positive ≠ negative) :
    pairwiseContrastiveStep rate energy positive negative negative =
      energy negative + rate := by
  simp [pairwiseContrastiveStep, pairwiseContrastiveGradient,
    distinct.symm]

/-- The sampled contrastive loss decreases by exactly twice the learning
rate in the tabular chart. -/
theorem pairwiseContrastiveLoss_after_step
    (rate : ℝ) (energy : Label → ℝ)
    {positive negative : Label}
    (distinct : positive ≠ negative) :
    pairwiseContrastiveLoss
        (pairwiseContrastiveStep rate energy positive negative)
        positive negative =
      pairwiseContrastiveLoss energy positive negative - 2 * rate := by
  rw [pairwiseContrastiveLoss,
    pairwiseContrastiveStep_positive rate energy distinct,
    pairwiseContrastiveStep_negative rate energy distinct]
  simp only [pairwiseContrastiveLoss]
  ring

/-- Negative boundary: if the same label is supplied on both sides, the
contrastive loss and its update vanish identically. -/
theorem equal_positive_negative_has_zero_update
    (rate : ℝ) (energy : Label → ℝ) (label : Label) :
    pairwiseContrastiveLoss energy label label = 0 ∧
      pairwiseContrastiveStep rate energy label label = energy := by
  constructor
  · simp [pairwiseContrastiveLoss]
  · funext candidate
    simp [pairwiseContrastiveStep, pairwiseContrastiveGradient]

end Pairwise

section SharedParameterBoundary

variable [DecidableEq Label]

/-- A one-parameter energy chart in which every label may share the same
trainable scalar through a label-specific coefficient. -/
def linearSharedEnergy
    (coefficient : Label → ℝ) (parameter : ℝ) (label : Label) : ℝ :=
  coefficient label * parameter

/-- Exact derivative coefficient of the pairwise loss in the shared scalar
parameter. -/
def linearSharedPairwiseGradient
    (coefficient : Label → ℝ) (positive negative : Label) : ℝ :=
  coefficient positive - coefficient negative

/-- Gradient-descent step on the shared scalar parameter. -/
def linearSharedPairwiseParameterStep
    (rate parameter : ℝ)
    (coefficient : Label → ℝ)
    (positive negative : Label) : ℝ :=
  parameter -
    rate * linearSharedPairwiseGradient coefficient positive negative

omit [DecidableEq Label] in
/-- The pairwise loss of the shared linear chart has an exact finite
increment, so the displayed parameter gradient is not assumed. -/
theorem linearSharedPairwiseLoss_increment_exact
    (coefficient : Label → ℝ)
    (parameter increment : ℝ)
    (positive negative : Label) :
    pairwiseContrastiveLoss
        (linearSharedEnergy coefficient (parameter + increment))
        positive negative =
      pairwiseContrastiveLoss
          (linearSharedEnergy coefficient parameter)
          positive negative +
        linearSharedPairwiseGradient coefficient positive negative *
          increment := by
  simp only [pairwiseContrastiveLoss, linearSharedEnergy,
    linearSharedPairwiseGradient]
  ring

end SharedParameterBoundary

/-! ## Executable strict separation -/

def zeroThreeEnergy : Fin 3 → ℝ := fun _ => 0

/-- Three label coefficients sharing one scalar parameter. -/
def sharedThreeCoefficient : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- With target zero and sampled negative one, label two is outside the
pairwise support but is changed by normalized likelihood. -/
theorem threeLabel_pairwise_vs_normalized_support_separation :
    pairwiseContrastiveStep 1 zeroThreeEnergy 0 1 2 = 0 ∧
      normalizedEnergyStep 1 zeroThreeEnergy 0 2 = (1 : ℝ) / 3 ∧
      pairwiseContrastiveStep 1 zeroThreeEnergy 0 1 2 ≠
        normalizedEnergyStep 1 zeroThreeEnergy 0 2 := by
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have two_ne_one : (2 : Fin 3) ≠ 1 := by decide
  norm_num [pairwiseContrastiveStep, pairwiseContrastiveGradient,
    normalizedEnergyStep, normalizedEnergyGradient,
    energyProbability, energyPartition, zeroThreeEnergy,
    two_ne_zero, two_ne_one]

/-- Positive fixture: the pairwise update sends the positive and negative
energies in opposite directions while leaving the third label fixed. -/
theorem threeLabel_pairwise_update :
    pairwiseContrastiveStep 2 zeroThreeEnergy 0 1 0 = -2 ∧
      pairwiseContrastiveStep 2 zeroThreeEnergy 0 1 1 = 2 ∧
      pairwiseContrastiveStep 2 zeroThreeEnergy 0 1 2 = 0 := by
  have zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
  have one_ne_zero : (1 : Fin 3) ≠ 0 := by decide
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have two_ne_one : (2 : Fin 3) ≠ 1 := by decide
  norm_num [pairwiseContrastiveStep, pairwiseContrastiveGradient,
    zeroThreeEnergy, zero_ne_one, one_ne_zero,
    two_ne_zero, two_ne_one]

/-- Negative boundary for support reasoning: the tabular pairwise update
leaves label two unchanged, while the corresponding shared-parameter update
changes label two even though it was not sampled. -/
theorem tabular_pair_support_does_not_imply_shared_parameter_noninterference :
    pairwiseContrastiveStep 1
        (linearSharedEnergy sharedThreeCoefficient 0) 0 1 2 =
      linearSharedEnergy sharedThreeCoefficient 0 2 ∧
    linearSharedEnergy sharedThreeCoefficient
        (linearSharedPairwiseParameterStep
          1 0 sharedThreeCoefficient 0 1) 2 ≠
      linearSharedEnergy sharedThreeCoefficient 0 2 := by
  have two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
  have two_ne_one : (2 : Fin 3) ≠ 1 := by decide
  norm_num [pairwiseContrastiveStep, pairwiseContrastiveGradient,
    linearSharedEnergy, linearSharedPairwiseParameterStep,
    linearSharedPairwiseGradient, sharedThreeCoefficient,
    two_ne_zero, two_ne_one]

#print axioms energyPartition_pos
#print axioms sum_energyProbability_eq_one
#print axioms normalizedEnergyStep_strictly_changes_nonTarget
#print axioms pairwiseContrastiveStep_changed_only_at_pair
#print axioms pairwiseContrastiveLoss_after_step
#print axioms equal_positive_negative_has_zero_update
#print axioms threeLabel_pairwise_vs_normalized_support_separation
#print axioms linearSharedPairwiseLoss_increment_exact
#print axioms tabular_pair_support_does_not_imply_shared_parameter_noninterference

end

end ContrastiveEnergyUpdateSupport

end Mettapedia.MachineLearning.ContinualLearning
