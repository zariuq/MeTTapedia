import Mathlib.Analysis.SpecialFunctions.Exp
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom

/-!
# Routing under action-set expansion

Adding a finite-logit action to a softmax changes the normalization even when
every old logit and parameter is frozen.  This module isolates that behavioral
boundary from parameter retention and records exact preservation conditions.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open Set
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom

/-- The probability assigned to an old action from its positive mass and the
old action set's total mass. -/
noncomputable def normalizedRouteWeight (weight oldTotal : ℝ) : ℝ :=
  weight / oldTotal

/-- The probability of the same old action after adding new routing mass. -/
noncomputable def expandedRouteWeight
    (weight oldTotal newMass : ℝ) : ℝ :=
  weight / (oldTotal + newMass)

@[simp] theorem expandedRouteWeight_zero_newMass
    (weight oldTotal : ℝ) :
    expandedRouteWeight weight oldTotal 0 =
      normalizedRouteWeight weight oldTotal := by
  simp [expandedRouteWeight, normalizedRouteWeight]

/-- Positive new routing mass strictly lowers every old action's positive
probability, despite unchanged old weights. -/
theorem expandedRouteWeight_strictly_decreases
    {weight oldTotal newMass : ℝ}
    (weightPositive : 0 < weight) (oldTotalPositive : 0 < oldTotal)
    (newMassPositive : 0 < newMass) :
    expandedRouteWeight weight oldTotal newMass <
      normalizedRouteWeight weight oldTotal := by
  rw [expandedRouteWeight, normalizedRouteWeight,
    div_lt_div_iff₀ (add_pos oldTotalPositive newMassPositive) oldTotalPositive]
  nlinarith

/-- A finite new softmax logit always contributes positive mass, so every old
action probability strictly decreases. -/
theorem finiteSoftmaxExpansion_strictly_decreases
    (oldLogit newLogit oldPartition : ℝ)
    (oldPartitionPositive : 0 < oldPartition) :
    expandedRouteWeight (Real.exp oldLogit) oldPartition
        (Real.exp newLogit) <
      normalizedRouteWeight (Real.exp oldLogit) oldPartition :=
  expandedRouteWeight_strictly_decreases (Real.exp_pos oldLogit)
    oldPartitionPositive (Real.exp_pos newLogit)

/-- Renormalization preserves the ordering among old actions because all old
masses receive the same positive denominator. -/
theorem expandedRouteWeight_old_order_iff
    {firstWeight secondWeight oldTotal newMass : ℝ}
    (expandedTotalPositive : 0 < oldTotal + newMass) :
    expandedRouteWeight firstWeight oldTotal newMass ≤
        expandedRouteWeight secondWeight oldTotal newMass ↔
      firstWeight ≤ secondWeight := by
  simpa [expandedRouteWeight] using
    (div_le_div_iff_of_pos_right expandedTotalPositive :
      firstWeight / (oldTotal + newMass) ≤
          secondWeight / (oldTotal + newMass) ↔
        firstWeight ≤ secondWeight)

/-- The output of a two-group router when each group has one aggregate value. -/
noncomputable def expandedRouteReadout
    (oldMass newMass oldValue newValue : ℝ) : ℝ :=
  (oldMass * oldValue + newMass * newValue) / (oldMass + newMass)

/-- Action-set growth is behavior-preserving when the new action is
observationally identical to the old aggregate. -/
theorem expandedRouteReadout_eq_of_values_eq
    {oldMass newMass oldValue newValue : ℝ}
    (valuesEqual : newValue = oldValue)
    (totalNonzero : oldMass + newMass ≠ 0) :
    expandedRouteReadout oldMass newMass oldValue newValue = oldValue := by
  subst newValue
  rw [expandedRouteReadout]
  field_simp

/-- The exact behavioral displacement caused by registering a new routed
action.  Routing mass and value mismatch appear as separate factors. -/
theorem expandedRouteReadout_sub_oldValue
    {oldMass newMass oldValue newValue : ℝ}
    (totalNonzero : oldMass + newMass ≠ 0) :
    expandedRouteReadout oldMass newMass oldValue newValue - oldValue =
      newMass * (newValue - oldValue) / (oldMass + newMass) := by
  rw [expandedRouteReadout]
  field_simp [totalNonzero]
  ring

/-- With nonzero new routing mass, exact aggregate no-regression is equivalent
to observational agreement between the new action and the old aggregate. -/
theorem expandedRouteReadout_eq_oldValue_iff
    {oldMass newMass oldValue newValue : ℝ}
    (newMassNonzero : newMass ≠ 0)
    (totalNonzero : oldMass + newMass ≠ 0) :
    expandedRouteReadout oldMass newMass oldValue newValue = oldValue ↔
      newValue = oldValue := by
  rw [expandedRouteReadout, div_eq_iff totalNonzero]
  constructor
  · intro aggregateEqual
    have mismatchZero : newMass * (newValue - oldValue) = 0 := by
      calc
        newMass * (newValue - oldValue) =
            (oldMass * oldValue + newMass * newValue) -
              oldValue * (oldMass + newMass) := by ring
        _ = 0 := sub_eq_zero.mpr aggregateEqual
    exact sub_eq_zero.mp ((mul_eq_zero.mp mismatchZero).resolve_left newMassNonzero)
  · intro valuesEqual
    subst newValue
    ring

/-- Negative fixture: frozen unit mass on an old zero-valued action changes
behavior when a unit-mass one-valued action is registered. -/
theorem frozen_old_route_new_action_changes_readout :
    expandedRouteReadout 1 1 0 1 = (1 / 2 : ℝ) ∧
      expandedRouteReadout 1 1 0 1 ≠ 0 := by
  norm_num [expandedRouteReadout]

/-- Negative fixture: a newly registered action can overtake every old action
even though the old masses and their internal ordering are unchanged. -/
theorem new_action_can_overtake_frozen_old_action :
    expandedRouteWeight 1 1 2 < expandedRouteWeight 2 1 2 := by
  norm_num [expandedRouteWeight]

/-! ## Finite-policy registration laws -/

/-- The old-action part of a finite routing policy after assigning total mass
`newMass` to newly registered actions.  Conditional proportions among old
actions are retained exactly. -/
noncomputable def retainedOldPolicyWeight
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (newMass : ℝ) (action : Action) : ℝ :=
  (1 - newMass) * routing.weight action

/-- The `L¹` distance between the zero-extended old policy and the expanded
policy: old-action drift plus the mass assigned to the new action group. -/
noncomputable def expandedPolicyL1Drift
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (newMass : ℝ) : ℝ :=
  (∑ action,
      |retainedOldPolicyWeight routing newMass action - routing.weight action|) +
    |newMass|

/-- Exact finite-policy law: registering actions with aggregate probability
`newMass` moves the zero-extended policy by `2 * newMass` in `L¹`, hence by
`newMass` in total variation.  Frozen old parameters do not prevent this
distributional change. -/
theorem expandedPolicyL1Drift_eq_two_mul_newMass
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) {newMass : ℝ}
    (newMassNonnegative : 0 ≤ newMass) :
    expandedPolicyL1Drift routing newMass = 2 * newMass := by
  have term (action : Action) :
      |retainedOldPolicyWeight routing newMass action -
          routing.weight action| =
        newMass * routing.weight action := by
    have difference :
        retainedOldPolicyWeight routing newMass action -
            routing.weight action =
          -(newMass * routing.weight action) := by
      simp only [retainedOldPolicyWeight]
      ring
    rw [difference, abs_neg, abs_of_nonneg]
    exact mul_nonneg newMassNonnegative (routing.nonneg action)
  simp_rw [expandedPolicyL1Drift, term]
  rw [← Finset.mul_sum, routing.sum_eq_one, mul_one,
    abs_of_nonneg newMassNonnegative]
  ring

/-- Total variation for the explicit old-policy/new-action registration
experiment. -/
noncomputable def expandedPolicyTotalVariation
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (newMass : ℝ) : ℝ :=
  expandedPolicyL1Drift routing newMass / 2

/-- The aggregate mass routed to new actions is exactly the total-variation
distance from the zero-extended old policy. -/
theorem expandedPolicyTotalVariation_eq_newMass
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) {newMass : ℝ}
    (newMassNonnegative : 0 ≤ newMass) :
    expandedPolicyTotalVariation routing newMass = newMass := by
  rw [expandedPolicyTotalVariation,
    expandedPolicyL1Drift_eq_two_mul_newMass routing newMassNonnegative]
  ring

/-- Expected scalar readout under a finite old routing policy. -/
noncomputable def finitePolicyReadout
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (value : Action → ℝ) : ℝ :=
  ∑ action, routing.weight action * value action

/-- Readout after reserving aggregate mass for newly registered actions. -/
noncomputable def registeredPolicyReadout
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (oldValue : Action → ℝ)
    (newMass newAggregateValue : ℝ) : ℝ :=
  (1 - newMass) * finitePolicyReadout routing oldValue +
    newMass * newAggregateValue

/-- Exact readout displacement under operator registration. -/
theorem registeredPolicyReadout_sub_old
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (oldValue : Action → ℝ)
    (newMass newAggregateValue : ℝ) :
    registeredPolicyReadout routing oldValue newMass newAggregateValue -
        finitePolicyReadout routing oldValue =
      newMass *
        (newAggregateValue - finitePolicyReadout routing oldValue) := by
  simp only [registeredPolicyReadout]
  ring

/-- A simplex readout remains inside any interval containing every action
value. -/
theorem finitePolicyReadout_mem_Icc
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (value : Action → ℝ)
    {lower upper : ℝ} (valueBounds : ∀ action, value action ∈ Icc lower upper) :
    finitePolicyReadout routing value ∈ Icc lower upper := by
  constructor
  · calc
      lower = ∑ action, routing.weight action * lower := by
        rw [← Finset.sum_mul, routing.sum_eq_one, one_mul]
      _ ≤ ∑ action, routing.weight action * value action := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (valueBounds action).1
            (routing.nonneg action)
      _ = finitePolicyReadout routing value := rfl
  · calc
      finitePolicyReadout routing value =
          ∑ action, routing.weight action * value action := rfl
      _ ≤ ∑ action, routing.weight action * upper := by
        exact Finset.sum_le_sum fun action _ =>
          mul_le_mul_of_nonneg_left (valueBounds action).2
            (routing.nonneg action)
      _ = upper := by
        rw [← Finset.sum_mul, routing.sum_eq_one, one_mul]

/-- Bounded-action behavior guarantee.  If old and new aggregate readouts lie
in one interval, registration changes the readout by at most interval width
times the new routing mass, which is exactly the total variation above. -/
theorem abs_registeredPolicyReadout_sub_old_le
    {Action : Type*} [Fintype Action]
    (routing : SimplexWeights Action) (oldValue : Action → ℝ)
    {newMass newAggregateValue lower upper : ℝ}
    (newMassNonnegative : 0 ≤ newMass)
    (oldBounds : ∀ action, oldValue action ∈ Icc lower upper)
    (newBounds : newAggregateValue ∈ Icc lower upper) :
    |registeredPolicyReadout routing oldValue newMass newAggregateValue -
        finitePolicyReadout routing oldValue| ≤
      newMass * (upper - lower) := by
  rw [registeredPolicyReadout_sub_old, abs_mul,
    abs_of_nonneg newMassNonnegative]
  apply mul_le_mul_of_nonneg_left _ newMassNonnegative
  have oldReadoutBounds := finitePolicyReadout_mem_Icc routing oldValue oldBounds
  rcases oldReadoutBounds with ⟨oldLower, oldUpper⟩
  rcases newBounds with ⟨newLower, newUpper⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith

#print axioms expandedRouteWeight_strictly_decreases
#print axioms finiteSoftmaxExpansion_strictly_decreases
#print axioms expandedRouteWeight_old_order_iff
#print axioms expandedRouteReadout_eq_of_values_eq
#print axioms expandedRouteReadout_sub_oldValue
#print axioms expandedRouteReadout_eq_oldValue_iff
#print axioms frozen_old_route_new_action_changes_readout
#print axioms new_action_can_overtake_frozen_old_action
#print axioms expandedPolicyL1Drift_eq_two_mul_newMass
#print axioms expandedPolicyTotalVariation_eq_newMass
#print axioms registeredPolicyReadout_sub_old
#print axioms finitePolicyReadout_mem_Icc
#print axioms abs_registeredPolicyReadout_sub_old_le

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
