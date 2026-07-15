import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.BackpropExactness

/-!
# Shared-latent predictive-coding DAGs

This file extends the scalar linear-Gaussian theory from chains to finite
computation DAGs.  An edge represents a parent slot, rather than merely a pair
of nodes, so parallel edges preserve the multiplicity of a hash-consed child
used in several slots.  The state still contains one latent per node.

The main result is an equilibrium error-force recursion: the force at a free
node is the sum of the transported forces from every parent occurrence.  This
is the finite scalar linearization of the arbitrary-graph predictive-coding
balance described by Millidge et al. (2020).  It is an error recursion, not a
claim that free-equilibrium parameter gradients equal forward backpropagation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Finite shared-latent DAG energy -/

/-- A finite scalar predictive-coding DAG.  Edges point from a child latent to
the parent prediction using it.  Distinct edges may have the same endpoints;
this records repeated parent slots without duplicating the shared latent. -/
structure SharedLatentDAG (Node Edge : Type*) [Fintype Node] [Fintype Edge] where
  source : Edge → Node
  target : Edge → Node
  rank : Node → ℕ
  forward : ∀ e, rank (source e) < rank (target e)
  gain : Edge → ℝ
  precision : Node → ℝ
  precision_pos : ∀ n, 0 < precision n
  offset : Node → ℝ
  clamped : Finset Node

section GeneralDAG

variable {Node Edge : Type*} [Fintype Node] [Fintype Edge] [DecidableEq Node]

/-- Node prediction error: the latent minus its offset and incoming linear
prediction. -/
noncomputable def dagResidual (G : SharedLatentDAG Node Edge)
    (z : Node → ℝ) (n : Node) : ℝ :=
  z n - G.offset n -
    ∑ e : Edge, if G.target e = n then G.gain e * z (G.source e) else 0

/-- Precision-weighted node prediction error. -/
noncomputable def dagResidualForce (G : SharedLatentDAG Node Edge)
    (z : Node → ℝ) (n : Node) : ℝ :=
  G.precision n * dagResidual G z n

/-- Sum-of-squares energy for a finite scalar shared-latent DAG. -/
noncomputable def dagEnergy (G : SharedLatentDAG Node Edge) (z : Node → ℝ) : ℝ :=
  ∑ n : Node, G.precision n * (dagResidual G z n) ^ 2

/-- States respecting every clamp in the DAG. -/
def dagClampedStateSet (G : SharedLatentDAG Node Edge)
    (boundary : Node → ℝ) : Set (Node → ℝ) :=
  {z | ∀ n ∈ G.clamped, z n = boundary n}

/-- A shared-latent DAG equilibrium minimizes energy on the clamped slice. -/
def dagEquilibrium (G : SharedLatentDAG Node Edge)
    (boundary z : Node → ℝ) : Prop :=
  z ∈ dagClampedStateSet G boundary ∧
    IsMinOn (dagEnergy G) (dagClampedStateSet G boundary) z

/-- Add a scalar displacement at exactly one node. -/
noncomputable def dagShift (z : Node → ℝ) (v : Node) (t : ℝ) : Node → ℝ :=
  fun n => if n = v then z n + t else z n

/-- Change in node `n`'s residual per unit displacement of node `v`. -/
noncomputable def dagResidualSensitivity
    (G : SharedLatentDAG Node Edge) (v n : Node) : ℝ :=
  (if n = v then 1 else 0) -
    ∑ e : Edge,
      if G.target e = n then
        if G.source e = v then G.gain e else 0
      else 0

theorem dagResidual_shift
    (G : SharedLatentDAG Node Edge) (z : Node → ℝ) (v n : Node) (t : ℝ) :
    dagResidual G (dagShift z v t) n =
      dagResidual G z n + t * dagResidualSensitivity G v n := by
  classical
  have hsum :
      (∑ e : Edge,
          if G.target e = n then G.gain e * dagShift z v t (G.source e) else 0) =
        (∑ e : Edge,
          if G.target e = n then G.gain e * z (G.source e) else 0) +
        t * ∑ e : Edge,
          if G.target e = n then
            if G.source e = v then G.gain e else 0
          else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases ht : G.target e = n
    · by_cases hs : G.source e = v
      · simp [ht, hs, dagShift]
        ring
      · simp [ht, hs, dagShift]
    · simp [ht]
  unfold dagResidual
  rw [hsum]
  unfold dagShift dagResidualSensitivity
  by_cases hn : n = v <;> simp [hn] <;> ring

/-- Reverse accumulation into a shared node.  The sum is over edge occurrences,
so repeated parent slots contribute repeatedly even when their source latent is
the same node. -/
noncomputable def dagParentErrorAggregate
    (G : SharedLatentDAG Node Edge) (z : Node → ℝ) (v : Node) : ℝ :=
  ∑ e : Edge,
    if G.source e = v then G.gain e * dagResidualForce G z (G.target e) else 0

/-- Linear coefficient of the energy change when one latent is displaced. -/
noncomputable def dagLinearCoefficient
    (G : SharedLatentDAG Node Edge) (z : Node → ℝ) (v : Node) : ℝ :=
  ∑ n : Node, dagResidualForce G z n * dagResidualSensitivity G v n

/-- Quadratic coefficient of the energy change when one latent is displaced. -/
noncomputable def dagQuadraticCoefficient
    (G : SharedLatentDAG Node Edge) (v : Node) : ℝ :=
  ∑ n : Node, G.precision n * (dagResidualSensitivity G v n) ^ 2

theorem dagEnergy_shift_sub
    (G : SharedLatentDAG Node Edge) (z : Node → ℝ) (v : Node) (t : ℝ) :
    dagEnergy G (dagShift z v t) - dagEnergy G z =
      t ^ 2 * dagQuadraticCoefficient G v + 2 * t * dagLinearCoefficient G z v := by
  classical
  unfold dagEnergy dagQuadraticCoefficient dagLinearCoefficient dagResidualForce
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [dagResidual_shift]
  ring

theorem dagShift_mem_clampedStateSet (G : SharedLatentDAG Node Edge)
    (boundary z : Node → ℝ) (v : Node) (t : ℝ)
    (hz : z ∈ dagClampedStateSet G boundary) (hv : v ∉ G.clamped) :
    dagShift z v t ∈ dagClampedStateSet G boundary := by
  intro n hn
  have hne : n ≠ v := by
    intro h
    subst n
    exact hv hn
  simp [dagShift, hne, hz n hn]

theorem dagEquilibrium_linearCoefficient_eq_zero
    (G : SharedLatentDAG Node Edge) (boundary z : Node → ℝ) (v : Node)
    (hv : v ∉ G.clamped) (heq : dagEquilibrium G boundary z) :
    dagLinearCoefficient G z v = 0 := by
  let Q := dagQuadraticCoefficient G v
  let L := dagLinearCoefficient G z v
  have hmin_forall :
      ∀ u ∈ dagClampedStateSet G boundary, dagEnergy G z ≤ dagEnergy G u := by
    simpa [IsMinOn, IsMinFilter] using heq.2
  have hpoly : ∀ t : ℝ, 0 ≤ Q * (t * t) + (2 * L) * t + 0 := by
    intro t
    have hshift :
        dagShift z v t ∈ dagClampedStateSet G boundary :=
      dagShift_mem_clampedStateSet G boundary z v t heq.1 hv
    have hle := hmin_forall (dagShift z v t) hshift
    have hnonneg : 0 ≤ dagEnergy G (dagShift z v t) - dagEnergy G z :=
      sub_nonneg.mpr hle
    rw [dagEnergy_shift_sub] at hnonneg
    dsimp [Q, L] at hnonneg ⊢
    nlinarith
  have hdisc := discrim_le_zero (a := Q) (b := 2 * L) (c := (0 : ℝ)) hpoly
  unfold discrim at hdisc
  have hLsq : L ^ 2 = 0 := by
    have hle : L ^ 2 ≤ 0 := by nlinarith
    exact le_antisymm hle (sq_nonneg L)
  exact sq_eq_zero_iff.mp hLsq

/-- The first-variation coefficient is own error force minus the sum of all
parent-slot transports. -/
theorem dagLinearCoefficient_eq_force_sub_parentAggregate
    (G : SharedLatentDAG Node Edge) (z : Node → ℝ) (v : Node) :
    dagLinearCoefficient G z v =
      dagResidualForce G z v - dagParentErrorAggregate G z v := by
  classical
  unfold dagLinearCoefficient dagResidualSensitivity
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hself :
      (∑ n : Node, dagResidualForce G z n * if n = v then 1 else 0) =
        dagResidualForce G z v := by
    simp
  rw [hself]
  congr 1
  calc
    (∑ n : Node, dagResidualForce G z n *
        ∑ e : Edge,
          if G.target e = n then
            if G.source e = v then G.gain e else 0
          else 0) =
      ∑ n : Node, ∑ e : Edge,
        dagResidualForce G z n *
          (if G.target e = n then
            if G.source e = v then G.gain e else 0
          else 0) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [Finset.mul_sum]
    _ = ∑ e : Edge, ∑ n : Node,
        dagResidualForce G z n *
          (if G.target e = n then
            if G.source e = v then G.gain e else 0
          else 0) := by
            rw [Finset.sum_comm]
    _ = dagParentErrorAggregate G z v := by
      unfold dagParentErrorAggregate
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hs : G.source e = v
      · simp [hs, mul_comm]
      · simp [hs]

/-- At a clamped minimum, the error force at each free shared latent
is exactly the sum of the transported error forces from all parent slots. -/
theorem sharedDAGEquilibriumError_satisfies_parentAggregationRecursion
    (G : SharedLatentDAG Node Edge) (boundary z : Node → ℝ) (v : Node)
    (hv : v ∉ G.clamped) (heq : dagEquilibrium G boundary z) :
    dagResidualForce G z v = dagParentErrorAggregate G z v := by
  have hzero := dagEquilibrium_linearCoefficient_eq_zero G boundary z v hv heq
  rw [dagLinearCoefficient_eq_force_sub_parentAggregate] at hzero
  exact sub_eq_zero.mp hzero

end GeneralDAG

/-! ## Verified-reference fixtures -/

/-- Two-node leaf-to-head shape used by the scalar oracle. -/
noncomputable def dagTwoNodeGraph : SharedLatentDAG (Fin 2) (Fin 1) where
  source := fun _ => 0
  target := fun _ => 1
  rank := fun n => n.val
  forward := by
    intro e
    fin_cases e
    norm_num
  gain := fun _ => 1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {1}

noncomputable def dagTwoNodeBoundary : Fin 2 → ℝ :=
  fun n => if n = 1 then 2 else 0

noncomputable def dagTwoNodeEquilibriumState : Fin 2 → ℝ :=
  fun n => (n.val : ℝ) + 1

theorem dagTwoNodeEquilibriumState_is_equilibrium :
    dagEquilibrium dagTwoNodeGraph dagTwoNodeBoundary dagTwoNodeEquilibriumState := by
  constructor
  · intro n hn
    fin_cases n
    · simp [dagTwoNodeGraph] at hn
    · norm_num [dagTwoNodeBoundary, dagTwoNodeEquilibriumState]
  · intro u hu
    have hu1 : u 1 = 2 := hu 1 (by simp [dagTwoNodeGraph])
    simp only [dagEnergy, dagResidual]
    simp [dagTwoNodeGraph, dagTwoNodeEquilibriumState, hu1]
    nlinarith [sq_nonneg (u 0 - 1)]

theorem dagTwoNode_errorRecursion_positive_example :
    dagResidualForce dagTwoNodeGraph dagTwoNodeEquilibriumState 0 =
      dagParentErrorAggregate dagTwoNodeGraph dagTwoNodeEquilibriumState 0 := by
  exact sharedDAGEquilibriumError_satisfies_parentAggregationRecursion
    dagTwoNodeGraph dagTwoNodeBoundary dagTwoNodeEquilibriumState 0
    (by simp [dagTwoNodeGraph]) dagTwoNodeEquilibriumState_is_equilibrium

/-- Oracle-shaped shared DAG: the leaf in node `0` fills two distinct slots of
the internal node `1`, which then feeds the clamped head `2`. -/
noncomputable def dagMultiParentGraph : SharedLatentDAG (Fin 3) (Fin 3) where
  source := fun e => if e.val = 2 then 1 else 0
  target := fun e => if e.val = 2 then 2 else 1
  rank := fun n => n.val
  forward := by
    intro e
    fin_cases e <;> norm_num
  gain := fun _ => 1
  precision := fun _ => 1
  precision_pos := by
    intro _n
    norm_num
  offset := fun _ => 0
  clamped := {2}

noncomputable def dagMultiParentBoundary : Fin 3 → ℝ :=
  fun n => if n.val = 2 then 6 else 0

noncomputable def dagMultiParentEquilibriumState : Fin 3 → ℝ :=
  fun n => if n.val = 0 then 2 else if n.val = 1 then 5 else 6

theorem dagMultiParentEquilibriumState_is_equilibrium :
    dagEquilibrium dagMultiParentGraph dagMultiParentBoundary
      dagMultiParentEquilibriumState := by
  constructor
  · intro n hn
    fin_cases n
    · simp [dagMultiParentGraph] at hn
    · simp [dagMultiParentGraph] at hn
    · norm_num [dagMultiParentBoundary, dagMultiParentEquilibriumState]
  · intro u hu
    have hu2 : u 2 = 6 := hu 2 (by simp [dagMultiParentGraph])
    simp only [dagEnergy, dagResidual]
    simp [Fin.sum_univ_succ, dagMultiParentGraph, dagMultiParentEquilibriumState, hu2]
    nlinarith [sq_nonneg (u 0 - 2),
      sq_nonneg ((u 0 - 2) - (u 1 - 5))]

theorem dagMultiParent_leaf_errorRecursion_positive_example :
    dagResidualForce dagMultiParentGraph dagMultiParentEquilibriumState 0 =
      dagParentErrorAggregate dagMultiParentGraph dagMultiParentEquilibriumState 0 := by
  exact sharedDAGEquilibriumError_satisfies_parentAggregationRecursion
    dagMultiParentGraph dagMultiParentBoundary dagMultiParentEquilibriumState 0
    (by simp [dagMultiParentGraph]) dagMultiParentEquilibriumState_is_equilibrium

theorem dagMultiParent_parentAggregate_counts_both_slots :
    dagParentErrorAggregate dagMultiParentGraph dagMultiParentEquilibriumState 0 = 2 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_succ, dagParentErrorAggregate, dagResidualForce, dagResidual,
    dagMultiParentGraph, dagMultiParentEquilibriumState, h20, h21]

/-- Negative fixture: keeping only one of the two parent-slot contributions
would give force `1`, while the shared leaf's equilibrium force is `2`. -/
theorem dagMultiParent_single_slot_is_incorrect_negative_example :
    dagResidualForce dagMultiParentGraph dagMultiParentEquilibriumState 0 ≠
      dagResidualForce dagMultiParentGraph dagMultiParentEquilibriumState 1 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Fin.sum_univ_succ, dagResidualForce, dagResidual, dagMultiParentGraph,
    dagMultiParentEquilibriumState, h20, h21]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
