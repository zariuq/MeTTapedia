import Mettapedia.Logic.MarkovLogicInfiniteUniqueness

/-!
# Infinite-MLN Boundary Stability

This module extracts the reusable boundary-insensitivity estimates that are
implicit in the descending-shell Dobrushin uniqueness proof.

The conceptual reading is open-ended ontology stability:

- a finite query region `Δ` represents the current local ontology or subsystem;
- different DLR witnesses represent different completions "at infinity";
- under a uniform Dobrushin budget, local disagreement decays geometrically
  with shell depth.

This does **not** yet compare two different MLN specifications `M₁ ⊆ M₂`.
Instead it isolates the core theorem needed for that future step: local query
answers are exponentially insensitive to the unresolved exterior.

Positive example: an expanding knowledge graph with uniformly bounded incoming
interaction budget has stable local query semantics.

Negative example: if the total incoming interaction is not uniformly bounded
below `1`, the present boundary-stability theorems do not apply and phase
transitions may occur.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open scoped ENNReal
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Finite-region assignment total variation decays geometrically with shell
depth under a uniform Dobrushin constant. -/
theorem finiteRegionAssignmentTotalVariation_le_card_mul_uniformConstant_pow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (Δ : Region Atom) :
    ∀ n : ℕ, M.finiteRegionAssignmentTotalVariation μ ν Δ ≤ (Δ.card : ℝ) * C ^ n := by
  intro n
  rcases M.exists_limitMarginalCoupling_sup_le_pow_of_uniformConstant
      hC_nonneg hC_lt_one hC_bound μ ν hμ hν (fun _ => false) n Δ with
    ⟨q, hqfst, hqsnd, hsup⟩
  calc
    M.finiteRegionAssignmentTotalVariation μ ν Δ
      ≤ (Δ.card : ℝ) *
          finiteRegionSupSeminorm Δ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
            exact M.finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
              μ ν Δ q hqfst hqsnd
    _ ≤ (Δ.card : ℝ) * C ^ n := by
          exact mul_le_mul_of_nonneg_left hsup (by positivity)

/-- Finite local-query discrepancy decays geometrically with shell depth under
a uniform Dobrushin constant. -/
theorem finiteRegionLocalQueryDiscrepancy_le_two_mul_card_mul_uniformConstant_pow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) :
    ∀ n : ℕ, M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  intro n
  calc
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q
      ≤ 2 * M.finiteRegionAssignmentTotalVariation μ ν Δ := by
          exact M.finiteRegionLocalQueryDiscrepancy_le_two_mul_assignmentTotalVariation μ ν Δ q
    _ ≤ 2 * ((Δ.card : ℝ) * C ^ n) := by
          have htv :=
            finiteRegionAssignmentTotalVariation_le_card_mul_uniformConstant_pow
              (M := M) hC_nonneg hC_lt_one hC_bound μ ν hμ hν Δ n
          linarith
    _ = 2 * (Δ.card : ℝ) * C ^ n := by ring

/-- User-facing packaging: under `PaperUniformSmallTotalInfluence`, every
finite-region assignment total variation admits a geometric shell-decay bound. -/
theorem finiteRegionAssignmentTotalVariation_le_geometric_of_uniformSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (Δ : Region Atom) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ, M.finiteRegionAssignmentTotalVariation μ ν Δ ≤ (Δ.card : ℝ) * C ^ n := by
  rcases M.finiteRegionPairwiseDobrushinConstant_le_uniform hM with ⟨C, hC_nonneg, hC_lt_one, hC_bound⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro n
  exact finiteRegionAssignmentTotalVariation_le_card_mul_uniformConstant_pow
    (M := M) hC_nonneg hC_lt_one hC_bound μ ν hμ hν Δ n

/-- User-facing packaging: under `PaperUniformSmallTotalInfluence`, every
finite local query admits a geometric shell-decay discrepancy bound. -/
theorem finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ, M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  rcases M.finiteRegionPairwiseDobrushinConstant_le_uniform hM with ⟨C, hC_nonneg, hC_lt_one, hC_bound⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro n
  exact finiteRegionLocalQueryDiscrepancy_le_two_mul_card_mul_uniformConstant_pow
    (M := M) hC_nonneg hC_lt_one hC_bound μ ν hμ hν Δ q n

end Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
