import Mathlib

/-!
# Group-local expert capacity

Lepikhin et al. (2020), *GShard: Scaling Giant Models with Conditional
Computation and Automatic Sharding*, partition a token batch into independently
processed groups and allocate every group a local capacity for each expert.
The local counters in Algorithm 1 admit a token only while its expert position
is below that capacity.

This file isolates the deterministic accounting theorem behind that design:
enforcing the same capacity in every group bounds the total accepted load by
the number of groups times the local capacity.  The converse is false: a
global bound alone permits one group to overflow while another is idle.

The result concerns accepted dispatches, not the algorithm's attempted-routing
counter, auxiliary loss, random second-expert routing, communication cost,
or empirical load balance.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

variable {Group : Type*}

/-- Total accepted load for one expert across independently routed groups. -/
def totalExpertLoad [Fintype Group] (accepted : Group → ℕ) : ℕ :=
  ∑ group, accepted group

/-- A uniform group-local cap composes into a global per-expert cap. -/
theorem totalExpertLoad_le_card_mul_capacity
    [Fintype Group]
    (accepted : Group → ℕ)
    (capacity : ℕ)
    (localCap : ∀ group, accepted group ≤ capacity) :
    totalExpertLoad accepted ≤ Fintype.card Group * capacity := by
  classical
  calc
    totalExpertLoad accepted =
        ∑ group : Group, accepted group := rfl
    _ ≤ ∑ _group : Group, capacity :=
      Finset.sum_le_sum fun group _ => localCap group
    _ = Fintype.card Group * capacity := by
      simp

/-- Saturating every group attains the composed bound exactly. -/
theorem totalExpertLoad_constant
    [Fintype Group]
    (capacity : ℕ) :
    totalExpertLoad (fun _ : Group => capacity) =
      Fintype.card Group * capacity := by
  classical
  simp [totalExpertLoad]

/-- With zero local capacity, every accepted group load must be zero. -/
theorem accepted_eq_zero_of_zero_local_capacity
    [Fintype Group]
    (accepted : Group → ℕ)
    (localCap : ∀ group, accepted group ≤ 0) :
    accepted = 0 := by
  funext group
  exact Nat.le_zero.mp (localCap group)

/-! ## Global-only accounting is insufficient -/

def imbalancedTwoGroupLoad : Fin 2 → ℕ :=
  ![2, 0]

/-- The total load can satisfy the composed bound while one group violates
the intended local capacity.  Local caps are therefore a strictly stronger
operational invariant than the corresponding aggregate inequality. -/
theorem global_capacity_does_not_imply_local_capacity :
    totalExpertLoad imbalancedTwoGroupLoad = 2 ∧
      totalExpertLoad imbalancedTwoGroupLoad ≤
        Fintype.card (Fin 2) * 1 ∧
      ¬ ∀ group, imbalancedTwoGroupLoad group ≤ 1 := by
  norm_num [totalExpertLoad, imbalancedTwoGroupLoad, Fin.sum_univ_succ]

/-- Two groups each accepting one token attain capacity two without a local
overflow. -/
theorem balanced_two_group_capacity :
    totalExpertLoad (![1, 1] : Fin 2 → ℕ) = 2 ∧
      ∀ group, (![1, 1] : Fin 2 → ℕ) group ≤ 1 := by
  norm_num [totalExpertLoad, Fin.sum_univ_succ]

#print axioms totalExpertLoad_le_card_mul_capacity
#print axioms totalExpertLoad_constant
#print axioms accepted_eq_zero_of_zero_local_capacity
#print axioms global_capacity_does_not_imply_local_capacity
#print axioms balanced_two_group_capacity

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
