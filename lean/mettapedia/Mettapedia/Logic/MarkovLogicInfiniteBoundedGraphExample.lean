import Mathlib.Logic.Equiv.Nat
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-!
# Infinite Bounded-Graph MLN Example

This module gives a bounded-degree infinite-graph example that is richer than
the one-dimensional belief line.  The atom space is `Bool × Nat`, interpreted
as two unbounded knowledge tracks indexed by `Nat`.

- `prior s n` softly biases node `(s,n)`;
- `along s n` softly propagates activation from `(s,n)` to `(s,n+1)`;
- `bridge n` softly couples `(false,n)` to `(true,n)`.

Every node participates in at most three interaction clauses:
two longitudinal clauses on its own track and one cross-track bridge.  The
uniform Dobrushin budget is therefore controlled by `|u| + |v| / 2`, where
`u` is the longitudinal influence weight and `v` is the cross-track bridge
weight.

Positive example: two evolving concept streams with moderate local inheritance
and moderate cross-context alignment admit a unique global Gibbs semantics.

Negative example: if `|u| + |v| / 2 >= 1`, the present uniqueness theorem no
longer applies; the specification may still have DLR measures, but uniqueness
is outside the proved regime.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteBoundedGraphExample

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-- Two-track countable graph nodes. -/
abbrev KnowledgeNode := Bool × Nat

/-- Clause ids for the bounded graph example. -/
inductive KnowledgeClauseId where
  | prior : Bool → Nat → KnowledgeClauseId
  | along : Bool → Nat → KnowledgeClauseId
  | bridge : Nat → KnowledgeClauseId
deriving DecidableEq

/-- Soft bias on a single node. -/
def knowledgePriorClause (s : Bool) (n : Nat) : GroundClause KnowledgeNode :=
  {Literal.pos (s, n)}

/-- Longitudinal influence within one track. -/
def knowledgeAlongClause (s : Bool) (n : Nat) : GroundClause KnowledgeNode :=
  {Literal.neg (s, n), Literal.pos (s, n + 1)}

/-- Cross-track influence at the same level. -/
def knowledgeBridgeClause (n : Nat) : GroundClause KnowledgeNode :=
  {Literal.neg (false, n), Literal.pos (true, n)}

/-- Underlying clause attached to a bounded-graph clause id. -/
def knowledgeClause : KnowledgeClauseId → GroundClause KnowledgeNode
  | .prior s n => knowledgePriorClause s n
  | .along s n => knowledgeAlongClause s n
  | .bridge n => knowledgeBridgeClause n

@[simp] theorem knowledgePriorClause_atoms (s : Bool) (n : Nat) :
    (knowledgePriorClause s n).atoms = ({(s, n)} : Finset KnowledgeNode) := by
  ext a
  simp [knowledgePriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem knowledgeAlongClause_atoms (s : Bool) (n : Nat) :
    (knowledgeAlongClause s n).atoms = ({(s, n), (s, n + 1)} : Finset KnowledgeNode) := by
  ext a
  simp [knowledgeAlongClause, GroundClause.atoms, Literal.atom]

@[simp] theorem knowledgeBridgeClause_atoms (n : Nat) :
    (knowledgeBridgeClause n).atoms =
      ({(false, n), (true, n)} : Finset KnowledgeNode) := by
  ext a
  simp [knowledgeBridgeClause, GroundClause.atoms, Literal.atom]

/-- Finite clause support for a finite bounded-graph region. -/
noncomputable def knowledgeRegionSupport (Λ : Region KnowledgeNode) : Finset KnowledgeClauseId :=
  (Λ.image (fun p => KnowledgeClauseId.prior p.1 p.2)) ∪
    ((Λ.image (fun p => KnowledgeClauseId.along p.1 p.2)) ∪
      (((Λ.image fun p => (p.1, Nat.pred p.2)).image
          (fun p => KnowledgeClauseId.along p.1 p.2)) ∪
        ((Λ.image Prod.snd).image KnowledgeClauseId.bridge)))

theorem knowledgeRegionSupport_sound
    {Λ : Region KnowledgeNode} {j : KnowledgeClauseId}
    (hj : j ∈ knowledgeRegionSupport Λ) :
    clauseTouchesRegion (knowledgeClause j) Λ := by
  rw [knowledgeRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hprior | hrest
  · rcases Finset.mem_image.mp hprior with ⟨p, hpΛ, rfl⟩
    refine ⟨p, ?_, hpΛ⟩
    simp [knowledgeClause]
  · rcases Finset.mem_union.mp hrest with halong | hrest
    · rcases Finset.mem_image.mp halong with ⟨p, hpΛ, rfl⟩
      refine ⟨p, ?_, hpΛ⟩
      simp [knowledgeClause]
    · rcases Finset.mem_union.mp hrest with hin | hbridge
      · rcases Finset.mem_image.mp hin with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
        by_cases hzero : a.2 = 0
        · rcases a with ⟨s, n⟩
          simp at hzero
          subst hzero
          have hp0 : p = (s, 0) := by
            simpa using hpred.symm
          subst hp0
          refine ⟨(s, 0), ?_, by simpa using haΛ⟩
          simp [knowledgeClause]
        · rcases a with ⟨s, n⟩
          have hn_pos : 0 < n := Nat.pos_of_ne_zero hzero
          have hp : p = (s, Nat.pred n) := by
            simpa using hpred.symm
          subst hp
          refine ⟨(s, n), ?_, by simpa using haΛ⟩
          have hmem : (s, n) = (s, n.pred + 1) := by
            exact congrArg (Prod.mk s) (Nat.succ_pred_eq_of_pos hn_pos).symm
          simpa [knowledgeClause, knowledgeAlongClause_atoms] using Or.inr hmem
      · rcases Finset.mem_image.mp hbridge with ⟨n, hn, rfl⟩
        rcases Finset.mem_image.mp hn with ⟨p, hpΛ, hpEq⟩
        refine ⟨p, ?_, hpΛ⟩
        rcases p with ⟨s, m⟩
        simp at hpEq
        simp [knowledgeClause, hpEq]

theorem knowledgeRegionSupport_complete
    {Λ : Region KnowledgeNode} {j : KnowledgeClauseId}
    (hj : clauseTouchesRegion (knowledgeClause j) Λ) :
    j ∈ knowledgeRegionSupport Λ := by
  rcases j with ⟨s, n⟩ | ⟨s, n⟩ | n
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (s, n) := by
      simpa [knowledgeClause] using haAtoms
    subst a
    rw [knowledgeRegionSupport]
    exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_image.mpr ⟨(s, n), haΛ, rfl⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (s, n) ∨ a = (s, n + 1) := by
      simpa [knowledgeClause] using haAtoms
    rw [knowledgeRegionSupport]
    rcases ha with haEq | haNext
    · have hmem : (s, n) ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨(s, n), hmem, rfl⟩
    · have hpredmem : (s, Nat.pred (n + 1)) ∈ Finset.image (fun p => (p.1, Nat.pred p.2)) Λ :=
        Finset.mem_image.mpr ⟨(s, n + 1), by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_image.mpr ⟨(s, Nat.pred (n + 1)), hpredmem, by simp⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (false, n) ∨ a = (true, n) := by
      simpa [knowledgeClause] using haAtoms
    rw [knowledgeRegionSupport]
    apply Finset.mem_union.mpr
    exact Or.inr <| Finset.mem_union.mpr <| Or.inr <| Finset.mem_union.mpr <| Or.inr <|
      Finset.mem_image.mpr <| by
        rcases ha with ha0 | ha1
        · refine ⟨n, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨(false, n), by simpa [ha0] using haΛ, rfl⟩
        · refine ⟨n, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨(true, n), by simpa [ha1] using haΛ, rfl⟩

/-- Initial-segment exhaustion of the two-track graph. -/
def knowledgeExhaustion : RegionExhaustion KnowledgeNode where
  region n := ({false, true} : Finset Bool).product (Finset.range (n + 1))
  monotone := by
    intro m n hmn a ha
    rcases Finset.mem_product.mp ha with ⟨haBool, haRange⟩
    exact Finset.mem_product.mpr ⟨haBool,
      Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp haRange) (Nat.succ_le_succ hmn)⟩
  exhaustive := by
    intro a
    rcases a with ⟨s, n⟩
    refine ⟨n, Finset.mem_product.mpr ?_⟩
    constructor
    · cases s <;> simp
    · exact Finset.mem_range.mpr (Nat.lt_succ_self n)

/-- Classical bounded-graph MLN with longitudinal weight `u` and bridge weight `v`. -/
noncomputable def knowledgeLadderClassicalSpec (u v : ℝ) :
    ClassicalInfiniteGroundMLNSpec KnowledgeNode KnowledgeClauseId where
  clause := knowledgeClause
  logWeight j := match j with
    | .prior _ _ => Real.log 2
    | .along _ _ => u
    | .bridge _ => v
  regionSupport := knowledgeRegionSupport
  regionSupport_sound := fun hj => knowledgeRegionSupport_sound hj
  regionSupport_complete := fun hj => knowledgeRegionSupport_complete hj

/-- The bounded graph has row sum at most `|u| + |v| / 2`. -/
theorem knowledgeLadderClassicalSpec_uniformSmallTotalInfluence
    {u v : ℝ} (hbudget : |u| + |v| / 2 < 1) :
    (knowledgeLadderClassicalSpec u v).PaperUniformSmallTotalInfluence := by
  refine ⟨|u| + |v| / 2, by positivity, hbudget, ?_⟩
  intro a
  rcases a with ⟨s, n⟩
  have hsupp :
      (knowledgeLadderClassicalSpec u v).regionSupport ({(s, n)} : Finset KnowledgeNode) =
        ({KnowledgeClauseId.prior s n, KnowledgeClauseId.along s n,
          KnowledgeClauseId.along s (Nat.pred n), KnowledgeClauseId.bridge n} :
            Finset KnowledgeClauseId) := by
    ext j
    simp [knowledgeLadderClassicalSpec, knowledgeRegionSupport]
    tauto
  have hrow :
      Finset.sum ((knowledgeLadderClassicalSpec u v).atomInteractionNeighborhood (s, n))
        (fun b => (knowledgeLadderClassicalSpec u v).pairwiseDobrushinCoefficient (s, n) b) =
        (1 / 2 : ℝ) * (knowledgeLadderClassicalSpec u v).atomTotalInfluence (s, n) := by
    rw [(knowledgeLadderClassicalSpec u v).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  have hprior_zero :
      (knowledgeLadderClassicalSpec u v).clauseInfluenceContribution (KnowledgeClauseId.prior s n) = 0 := by
    apply (knowledgeLadderClassicalSpec u v).clauseInfluenceContribution_eq_zero_of_card_le_one
    simp [knowledgeLadderClassicalSpec, knowledgeClause, knowledgePriorClause_atoms]
  by_cases hzero : n = 0
  · subst hzero
    have htot0 :
        (knowledgeLadderClassicalSpec u v).atomTotalInfluence (s, 0) = |u| + |v| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        knowledgeLadderClassicalSpec, knowledgeClause, knowledgeAlongClause_atoms,
        knowledgeBridgeClause_atoms]
    rw [htot0]
    nlinarith [abs_nonneg u, abs_nonneg v]
  · have hpred_ne : Nat.pred n ≠ n := by
      exact Nat.ne_of_lt (Nat.pred_lt hzero)
    have hnpred : n ≠ Nat.pred n := by
      intro h
      exact hpred_ne h.symm
    have htot :
        (knowledgeLadderClassicalSpec u v).atomTotalInfluence (s, n) = 2 * |u| + |v| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
            knowledgeLadderClassicalSpec, knowledgeClause]
          ring_nf
        · intro h
          simp at h
          exact hnpred h
      · simp
    rw [htot]
    nlinarith [abs_nonneg u, abs_nonneg v]

/-- Existence for the bounded-graph example on the countable atom type
`Bool × Nat`. -/
theorem exists_knowledgeLadder_fixedRegionCylinderDLR
    (u v : ℝ) (ξ : BoundaryCondition KnowledgeNode) :
    ∃ μ : Measure (InfiniteWorld KnowledgeNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (knowledgeLadderClassicalSpec u v).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (knowledgeLadderClassicalSpec u v).exists_fixedRegionCylinderDLR_of_equiv
      knowledgeExhaustion ξ Equiv.boolProdNatEquivNat.symm

/-- End-to-end uniqueness for the bounded graph under the Dobrushin budget
`|u| + |v| / 2 < 1`. -/
theorem knowledgeLadder_uniqueMeasure
    {u v : ℝ} (hbudget : |u| + |v| / 2 < 1) :
    (knowledgeLadderClassicalSpec u v).PaperUniqueMeasure :=
  (knowledgeLadderClassicalSpec u v).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (knowledgeLadderClassicalSpec_uniformSmallTotalInfluence hbudget)

/-- End-to-end WM bridge uniqueness for the bounded graph. -/
theorem knowledgeLadder_wmBridge_unique
    {u v : ℝ} (hbudget : |u| + |v| / 2 < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld KnowledgeNode))
    (hμ : FixedRegionCylinderDLR
      (knowledgeLadderClassicalSpec u v).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld KnowledgeNode)))
    (hν : FixedRegionCylinderDLR
      (knowledgeLadderClassicalSpec u v).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld KnowledgeNode)))
    (q : ConstraintQuery KnowledgeNode) :
    (infiniteMLNMassSemantics (knowledgeLadderClassicalSpec u v) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (knowledgeLadderClassicalSpec u v) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (knowledgeLadderClassicalSpec u v)
    (knowledgeLadderClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν q

/-- Quantitative local stability for the bounded graph, reusing the extracted
boundary-stability layer. -/
theorem knowledgeLadder_localQueryDiscrepancy_le_geometric
    {u v : ℝ} (hbudget : |u| + |v| / 2 < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld KnowledgeNode))
    (hμ : FixedRegionCylinderDLR
      (knowledgeLadderClassicalSpec u v).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld KnowledgeNode)))
    (hν : FixedRegionCylinderDLR
      (knowledgeLadderClassicalSpec u v).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld KnowledgeNode)))
    (Δ : Region KnowledgeNode)
    (q : LocalConstraintQuery KnowledgeNode Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (knowledgeLadderClassicalSpec u v).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := knowledgeLadderClassicalSpec u v)
    (knowledgeLadderClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν Δ q

end Mettapedia.Logic.MarkovLogicInfiniteBoundedGraphExample
