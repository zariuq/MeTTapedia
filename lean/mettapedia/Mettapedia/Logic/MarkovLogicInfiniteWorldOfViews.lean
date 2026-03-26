import Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability

/-!
# Infinite World-of-Views MLN

This module packages a simple heterogeneous "world of views" example:

- atoms are indexed by `Nat`, representing a countable family of agents;
- `bias n` is the local prior bias of agent `n`;
- `trust n` is the influence weight from agent `n` to agent `n + 1`.

Unlike the uniform belief line, the influence weights may vary from agent to
agent.  The semantics is still unique whenever the per-agent incoming trust
budget is uniformly bounded below the Dobrushin threshold.

Positive example: a distributed sense-making process with heterogeneous but
uniformly bounded trust weights has a unique global equilibrium.

Negative example: if some agents participate in an arbitrarily strong
reinforcing echo chamber, the present theorem does not guarantee uniqueness.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteWorldOfViews

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample

/-- Heterogeneous world-of-views specification: one prior weight per agent and
one trust weight per directed neighbour influence edge. -/
noncomputable def worldOfViewsClassicalSpec
    (bias trust : Nat → ℝ) :
    ClassicalInfiniteGroundMLNSpec Nat BeliefClauseId where
  clause := beliefLineClause
  logWeight j := match j with
    | .prior n => bias n
    | .influence n => trust n
  regionSupport := beliefLineRegionSupport
  regionSupport_sound := fun hj => beliefLineRegionSupport_sound hj
  regionSupport_complete := fun hj => beliefLineRegionSupport_complete hj

/-- Uniform Dobrushin condition for heterogeneous trust weights.

If every agent's local row sum `( |trust n| + |trust (pred n)| ) / 2` is
bounded by the same `C < 1`, then the world-of-views MLN satisfies
`PaperUniformSmallTotalInfluence`. -/
theorem worldOfViewsClassicalSpec_uniformSmallTotalInfluence
    {bias trust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat, (|trust n| + |trust (Nat.pred n)|) / 2 ≤ C) :
    (worldOfViewsClassicalSpec bias trust).PaperUniformSmallTotalInfluence := by
  rcases htrust with ⟨C, hC_nonneg, hC_lt_one, hrowBound⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro a
  have hsupp :
      (worldOfViewsClassicalSpec bias trust).regionSupport ({a} : Finset Nat) =
        ({BeliefClauseId.prior a, BeliefClauseId.influence a,
          BeliefClauseId.influence (Nat.pred a)} : Finset BeliefClauseId) := by
    ext j
    simp [worldOfViewsClassicalSpec, beliefLineRegionSupport]
    tauto
  have hrow :
      Finset.sum ((worldOfViewsClassicalSpec bias trust).atomInteractionNeighborhood a)
        (fun b => (worldOfViewsClassicalSpec bias trust).pairwiseDobrushinCoefficient a b) =
        (1 / 2 : ℝ) * (worldOfViewsClassicalSpec bias trust).atomTotalInfluence a := by
    rw [(worldOfViewsClassicalSpec bias trust).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  by_cases ha : a = 0
  · subst ha
    have htot0 :
        (worldOfViewsClassicalSpec bias trust).atomTotalInfluence 0 = |trust 0| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        worldOfViewsClassicalSpec, beliefLineClause, beliefLineInfluenceClause_atoms]
    rw [htot0]
    have hbound0 : |trust 0| ≤ C := by
      simpa using hrowBound 0
    have hhalf0 : (1 / 2 : ℝ) * |trust 0| ≤ C := by
      nlinarith [hbound0, abs_nonneg (trust 0)]
    exact hhalf0
  · have hpred_ne : Nat.pred a ≠ a := by
      exact Nat.ne_of_lt (Nat.pred_lt ha)
    have hprior_zero :
        (worldOfViewsClassicalSpec bias trust).clauseInfluenceContribution (BeliefClauseId.prior a) = 0 := by
      apply (worldOfViewsClassicalSpec bias trust).clauseInfluenceContribution_eq_zero_of_card_le_one
      simp [worldOfViewsClassicalSpec, beliefLineClause, beliefLinePriorClause_atoms]
    have hsuminfl :
        ({BeliefClauseId.influence a, BeliefClauseId.influence (Nat.pred a)} :
            Finset BeliefClauseId).sum
          (fun j => (worldOfViewsClassicalSpec bias trust).clauseInfluenceContribution j) =
          |trust a| + |trust (Nat.pred a)| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          worldOfViewsClassicalSpec, beliefLineClause, beliefLineInfluenceClause_atoms]
      · intro h
        injection h with hEq
        exact hpred_ne hEq.symm
    have htot :
        (worldOfViewsClassicalSpec bias trust).atomTotalInfluence a =
          |trust a| + |trust (Nat.pred a)| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, hsuminfl]
      · simp
    rw [htot]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrowBound a

/-- Existence for the heterogeneous world-of-views MLN. -/
theorem exists_worldOfViews_fixedRegionCylinderDLR
    (bias trust : Nat → ℝ) (ξ : BoundaryCondition Nat) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (worldOfViewsClassicalSpec bias trust).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (worldOfViewsClassicalSpec bias trust).exists_fixedRegionCylinderDLR_of_equiv
      beliefLineExhaustion ξ (Equiv.refl Nat)

/-- End-to-end uniqueness for heterogeneous world-of-views models. -/
theorem worldOfViews_uniqueMeasure
    {bias trust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat, (|trust n| + |trust (Nat.pred n)|) / 2 ≤ C) :
    (worldOfViewsClassicalSpec bias trust).PaperUniqueMeasure :=
  (worldOfViewsClassicalSpec bias trust).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (worldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)

/-- The WM bridge is specification-determined under the same trust-budget
hypothesis. -/
theorem worldOfViews_wmBridge_unique
    {bias trust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat, (|trust n| + |trust (Nat.pred n)|) / 2 ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (worldOfViewsClassicalSpec bias trust).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (worldOfViewsClassicalSpec bias trust).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (q : ConstraintQuery Nat) :
    (infiniteMLNMassSemantics (worldOfViewsClassicalSpec bias trust) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (worldOfViewsClassicalSpec bias trust) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (worldOfViewsClassicalSpec bias trust)
    (worldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)
    μ ν hμ hν q

/-- Quantitative local boundary-insensitivity for world-of-views queries. -/
theorem worldOfViews_localQueryDiscrepancy_le_geometric
    {bias trust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat, (|trust n| + |trust (Nat.pred n)|) / 2 ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (worldOfViewsClassicalSpec bias trust).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (worldOfViewsClassicalSpec bias trust).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (Δ : Region Nat)
    (q : LocalConstraintQuery Nat Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (worldOfViewsClassicalSpec bias trust).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := worldOfViewsClassicalSpec bias trust)
    (worldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)
    μ ν hμ hν Δ q

end Mettapedia.Logic.MarkovLogicInfiniteWorldOfViews
