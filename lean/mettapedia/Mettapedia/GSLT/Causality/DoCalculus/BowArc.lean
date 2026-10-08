import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mettapedia.GSLT.Causality.DoCalculus.TruncatedFactorization

/-!
# Bow-arc: an effect that is not identified

The graph `U → X → Y` together with the confounding arc `U → Y` is the bow.
Two Markovian conditional tables on that graph can induce the same joint and
different laws of `Y` under `do(X = true)`. The disagreement sits off the
observational support of `Y`'s parents, which is exactly the region the
intervention selects.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open scoped BigOperators ENNReal

/-- Vertices of the bow: confounder, treatment, outcome. -/
inductive Bow
  | u
  | x
  | y
  deriving DecidableEq

instance : Fintype Bow where
  elems := {Bow.u, Bow.x, Bow.y}
  complete := by intro v; cases v <;> simp

/-- `U → X → Y` and `U → Y`. -/
def bowGraph : DirectedGraph Bow where
  edges a b :=
    (a = .u ∧ b = .x) ∨ (a = .u ∧ b = .y) ∨ (a = .x ∧ b = .y)

instance : DecidableRel bowGraph.edges := fun a b => by
  unfold bowGraph
  infer_instance

/-- Rank increases along every edge, so the bow is acyclic. -/
def bowRank : Bow → ℕ
  | .u => 0
  | .x => 1
  | .y => 2

lemma bow_edge_increases {a b : Bow} (h : bowGraph.edges a b) : bowRank a < bowRank b := by
  cases a <;> cases b <;> simp [bowGraph, bowRank] at h ⊢

lemma bow_reachable_rank {a b : Bow} (h : bowGraph.Reachable a b) : bowRank a ≤ bowRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (bow_edge_increases hedge)) ih

/-- The bow has no directed cycle. -/
lemma bowAcyclic : bowGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (bow_edge_increases hedge) (bow_reachable_rank hreach)

/-- A fair coin, built as a finite mass function rather than a Bernoulli parameter. -/
noncomputable def fairBit : PMF Bool :=
  PMF.ofFintype (fun _ => (2 : ℝ≥0∞)⁻¹) <| by
    have huniv : (Finset.univ : Finset Bool) = insert false {true} := by
      ext b
      cases b <;> simp
    rw [huniv, Finset.sum_insert (by simp), Finset.sum_singleton, ENNReal.inv_two_add_inv_two]

lemma fairBit_apply (b : Bool) : fairBit b = (2 : ℝ≥0∞)⁻¹ := by
  simp [fairBit]

lemma fairBit_sum : ∑ b : Bool, fairBit b = 1 := by
  simp [fairBit]
  exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

lemma bow_u_parent_x :
    Bow.u ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.x := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph]

lemma bow_u_parent_y :
    Bow.u ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph]

lemma bow_x_parent_y :
    Bow.x ∈ (network (β := Bool) bowGraph bowAcyclic).parents Bow.y := by
  simp [BayesianNetwork.parents, DirectedGraph.parents, bowGraph]

/-- Model 1: `X` copies `U`, and `Y` copies `X`. -/
noncomputable def bowCPT1 : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .u => fairBit
    | .x => PMF.pure (pa .u bow_u_parent_x)
    | .y => PMF.pure (pa .x bow_x_parent_y)

/-- Model 2: `X` copies `U`, and `Y` copies `U`, ignoring `X`. -/
noncomputable def bowCPT2 : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT where
  cpt := fun v pa =>
    match v with
    | .u => fairBit
    | .x => PMF.pure (pa .u bow_u_parent_x)
    | .y => PMF.pure (pa .u bow_u_parent_y)

/-- Read a configuration off three bits. -/
def bowOf (bu bx byy : Bool) : Bow → Bool
  | .u => bu
  | .x => bx
  | .y => byy

lemma prod_bow (g : Bow → ℝ≥0∞) : ∏ v, g v = g .u * (g .x * g .y) := by
  have huniv : (Finset.univ : Finset Bow) = insert .u (insert .x {.y}) := by
    ext v
    cases v <;> simp
  rw [huniv, Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]

lemma sum_bool (h : Bool → ℝ≥0∞) : ∑ b, h b = h false + h true := by
  have huniv : (Finset.univ : Finset Bool) = insert false {true} := by
    ext b
    cases b <;> simp
  rw [huniv, Finset.sum_insert (by simp), Finset.sum_singleton]

lemma sum_bow (g : (Bow → Bool) → ℝ≥0∞) :
    ∑ f, g f = ∑ bu, ∑ bx, ∑ byy, g (bowOf bu bx byy) := by
  let e : (Bow → Bool) ≃ Bool × Bool × Bool :=
    { toFun := fun f => (f .u, f .x, f .y)
      invFun := fun p => bowOf p.1 p.2.1 p.2.2
      left_inv := by
        intro f
        ext v
        cases v <;> rfl
      right_inv := by
        rintro ⟨bu, bx, byy⟩
        rfl }
  rw [← Equiv.sum_comp e.symm g]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bu _ => ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun bx _ => ?_
  refine Finset.sum_congr rfl fun byy _ => ?_
  rfl

lemma node1_u (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT1 f .u = fairBit (f .u) := by
  simp [DiscreteCPT.nodeProb, bowCPT1]

lemma node1_x (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT1 f .x = PMF.pure (f .u) (f .x) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, bowCPT1]

lemma node1_y (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT1 f .y = PMF.pure (f .x) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, bowCPT1]

lemma node2_u (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT2 f .u = fairBit (f .u) := by
  simp [DiscreteCPT.nodeProb, bowCPT2]

lemma node2_x (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT2 f .x = PMF.pure (f .u) (f .x) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, bowCPT2]

lemma node2_y (f : Bow → Bool) :
    DiscreteCPT.nodeProb bowCPT2 f .y = PMF.pure (f .u) (f .y) := by
  simp [DiscreteCPT.nodeProb, DiscreteCPT.parentAssignOfConfig, bowCPT2]

lemma joint1_factor (f : Bow → Bool) :
    bowCPT1.jointWeight f = fairBit (f .u) * (PMF.pure (f .u) (f .x) * PMF.pure (f .x) (f .y)) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_bow]
  simp [node1_u, node1_x, node1_y]

lemma joint2_factor (f : Bow → Bool) :
    bowCPT2.jointWeight f = fairBit (f .u) * (PMF.pure (f .u) (f .x) * PMF.pure (f .u) (f .y)) := by
  unfold DiscreteCPT.jointWeight
  rw [prod_bow]
  simp [node2_u, node2_x, node2_y]

/-- Both models put mass `1/2` on the two constant configurations and `0` elsewhere. -/
lemma bow_factor_support (fu fx fy : Bool) :
    fairBit fu * (PMF.pure fu fx * PMF.pure fx fy) =
      if fx = fu ∧ fy = fu then fairBit fu else 0 := by
  cases fu <;> cases fx <;> cases fy <;> simp [fairBit_apply]

lemma bow_factor_support₂ (fu fx fy : Bool) :
    fairBit fu * (PMF.pure fu fx * PMF.pure fu fy) =
      if fx = fu ∧ fy = fu then fairBit fu else 0 := by
  cases fu <;> cases fx <;> cases fy <;> simp [fairBit_apply]

/-- **The two bows have the same observational joint.** -/
theorem bow_joint_agree (f : Bow → Bool) :
    bowCPT1.jointWeight f = bowCPT2.jointWeight f := by
  rw [joint1_factor, joint2_factor, bow_factor_support, bow_factor_support₂]

/-- Set `X` to `true` and leave the other variables free. -/
def doXTrue : Bow → Option Bool :=
  fun v => if v = .x then some true else none

lemma trunc1_weight (f : Bow → Bool) :
    truncatedWeight bowGraph bowAcyclic bowCPT1 doXTrue f =
      (if f .x = true then 1 else 0) *
        (fairBit (f .u) * PMF.pure (f .x) (f .y)) := by
  unfold truncatedWeight
  rw [prod_bow]
  have hu : truncatedFactor bowGraph bowAcyclic bowCPT1 doXTrue f .u = fairBit (f .u) := by
    simp [truncatedFactor, doXTrue, ← node1_u, cptAt_eq_nodeProb]
  have hx : truncatedFactor bowGraph bowAcyclic bowCPT1 doXTrue f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, doXTrue]
  have hy : truncatedFactor bowGraph bowAcyclic bowCPT1 doXTrue f .y =
      PMF.pure (f .x) (f .y) := by
    have hne : Bow.y ≠ Bow.x := by decide
    simp only [truncatedFactor, doXTrue, if_neg hne, cptAt_eq_nodeProb, node1_y]
  simp [hu, hx, hy, mul_comm]

lemma trunc2_weight (f : Bow → Bool) :
    truncatedWeight bowGraph bowAcyclic bowCPT2 doXTrue f =
      (if f .x = true then 1 else 0) *
        (fairBit (f .u) * PMF.pure (f .u) (f .y)) := by
  unfold truncatedWeight
  rw [prod_bow]
  have hu : truncatedFactor bowGraph bowAcyclic bowCPT2 doXTrue f .u = fairBit (f .u) := by
    simp [truncatedFactor, doXTrue, ← node2_u, cptAt_eq_nodeProb]
  have hx : truncatedFactor bowGraph bowAcyclic bowCPT2 doXTrue f .x =
      if f .x = true then 1 else 0 := by
    simp [truncatedFactor, doXTrue]
  have hy : truncatedFactor bowGraph bowAcyclic bowCPT2 doXTrue f .y = PMF.pure (f .u) (f .y) := by
    have hne : Bow.y ≠ Bow.x := by decide
    simp only [truncatedFactor, doXTrue, if_neg hne, cptAt_eq_nodeProb, node2_y]
  simp [hu, hx, hy, mul_comm]

/-- Mass of `Y = y` under `do(X = true)`. -/
noncomputable def bowDoMass (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT)
    (y : Bool) : ℝ≥0∞ :=
  ∑ f, if f .y = y then truncatedWeight bowGraph bowAcyclic cpt doXTrue f else 0

/-- **In model 1, `do(X = true)` forces `Y = true`.** -/
theorem bow_do_model1 : bowDoMass bowCPT1 true = 1 := by
  unfold bowDoMass
  rw [sum_bow]
  simp_rw [trunc1_weight, bowOf]
  simp_rw [sum_bool]
  simp [fairBit_apply, ENNReal.inv_two_add_inv_two]

/-- **In model 2, `do(X = true)` leaves `Y` a fair coin.** -/
theorem bow_do_model2 : bowDoMass bowCPT2 true = (2 : ℝ≥0∞)⁻¹ := by
  unfold bowDoMass
  rw [sum_bow]
  simp_rw [trunc2_weight, bowOf]
  simp_rw [sum_bool]
  simp [fairBit_apply]

lemma one_ne_inv_two : (1 : ℝ≥0∞) ≠ (2 : ℝ≥0∞)⁻¹ := by
  intro h
  have hc : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [← h] at hc
  simp at hc

/-- **The effect of `X` on `Y` is not identified from the observational joint.**

The two models agree on every configuration and disagree on
`P(Y = true | do(X = true))`, which is `1` in the first and `1/2` in the second.
-/
theorem bow_effect_not_identified :
    (∀ f, bowCPT1.jointWeight f = bowCPT2.jointWeight f) ∧
      bowDoMass bowCPT1 true ≠ bowDoMass bowCPT2 true := by
  refine ⟨bow_joint_agree, ?_⟩
  rw [bow_do_model1, bow_do_model2]
  exact one_ne_inv_two

end Mettapedia.GSLT.Causality.DoCalculus
