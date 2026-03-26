import Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability

/-!
# Infinite Bidirectional World-of-Views MLN

This module enriches the earlier world-of-views example by allowing two
independent local trust channels on the countable agent line:

- `forwardTrust n` weights the clause `Believes n -> Believes (n + 1)`;
- `backwardTrust n` weights the clause `Believes (n + 1) -> Believes n`.

The result is still a bounded-neighborhood infinite MLN, but now every adjacent
pair of agents may influence each other with different strengths.  This is a
better fit for neighborhood-style social semantics than the purely one-way
chain.

Positive example: a distributed sense-making process with heterogeneous but
uniformly bounded forward and backward trust has a unique global equilibrium.

Negative example: if the combined incoming/outgoing trust around some agent can
exceed the global Dobrushin budget, the present theorem no longer guarantees
uniqueness.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteBidirectionalWorldOfViews

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

/-- Clause ids for bidirectional local trust on the countable agent line. -/
inductive BidirectionalViewClauseId where
  | prior : Nat → BidirectionalViewClauseId
  | forward : Nat → BidirectionalViewClauseId
  | backward : Nat → BidirectionalViewClauseId
deriving DecidableEq

/-- Soft bias toward believing at site `n`. -/
def bidirectionalViewPriorClause (n : Nat) : GroundClause Nat :=
  {Literal.pos n}

/-- Forward trust: if `n` believes, `n + 1` is nudged to believe. -/
def bidirectionalViewForwardClause (n : Nat) : GroundClause Nat :=
  {Literal.neg n, Literal.pos (n + 1)}

/-- Backward trust: if `n + 1` believes, `n` is nudged to believe. -/
def bidirectionalViewBackwardClause (n : Nat) : GroundClause Nat :=
  {Literal.neg (n + 1), Literal.pos n}

/-- The underlying clause attached to a bidirectional view clause id. -/
def bidirectionalViewClause : BidirectionalViewClauseId → GroundClause Nat
  | .prior n => bidirectionalViewPriorClause n
  | .forward n => bidirectionalViewForwardClause n
  | .backward n => bidirectionalViewBackwardClause n

@[simp] theorem bidirectionalViewPriorClause_atoms (n : Nat) :
    (bidirectionalViewPriorClause n).atoms = ({n} : Finset Nat) := by
  ext a
  simp [bidirectionalViewPriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem bidirectionalViewForwardClause_atoms (n : Nat) :
    (bidirectionalViewForwardClause n).atoms = ({n, n + 1} : Finset Nat) := by
  ext a
  simp [bidirectionalViewForwardClause, GroundClause.atoms, Literal.atom]

@[simp] theorem bidirectionalViewBackwardClause_atoms (n : Nat) :
    (bidirectionalViewBackwardClause n).atoms = ({n, n + 1} : Finset Nat) := by
  ext a
  simp [bidirectionalViewBackwardClause, GroundClause.atoms, Literal.atom, or_comm]

/-- Finite clause support for a finite set of agents:
priors on the region, plus incoming and outgoing trust clauses in both
directions. -/
noncomputable def bidirectionalViewRegionSupport (Λ : Region Nat) :
    Finset BidirectionalViewClauseId :=
  (Λ.image BidirectionalViewClauseId.prior) ∪
    ((Λ.image BidirectionalViewClauseId.forward) ∪
      (((Λ.image Nat.pred).image BidirectionalViewClauseId.forward) ∪
        ((Λ.image BidirectionalViewClauseId.backward) ∪
          ((Λ.image Nat.pred).image BidirectionalViewClauseId.backward))))

theorem bidirectionalViewRegionSupport_sound
    {Λ : Region Nat} {j : BidirectionalViewClauseId}
    (hj : j ∈ bidirectionalViewRegionSupport Λ) :
    clauseTouchesRegion (bidirectionalViewClause j) Λ := by
  rw [bidirectionalViewRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hprior | hrest
  · rcases Finset.mem_image.mp hprior with ⟨n, hnΛ, rfl⟩
    refine ⟨n, ?_, hnΛ⟩
    simp [bidirectionalViewClause]
  · rcases Finset.mem_union.mp hrest with hforwardOut | hrest
    · rcases Finset.mem_image.mp hforwardOut with ⟨n, hnΛ, rfl⟩
      refine ⟨n, ?_, hnΛ⟩
      simp [bidirectionalViewClause]
    · rcases Finset.mem_union.mp hrest with hforwardIn | hrest
      · rcases Finset.mem_image.mp hforwardIn with ⟨m, hm, rfl⟩
        rcases Finset.mem_image.mp hm with ⟨a, haΛ, hpred⟩
        by_cases hzero : a = 0
        · subst hzero
          have hm0 : m = 0 := by simpa using hpred.symm
          subst hm0
          refine ⟨0, ?_, by simpa using haΛ⟩
          simp [bidirectionalViewClause]
        · have ha_pos : 0 < a := Nat.pos_of_ne_zero hzero
          have haeq : a = m + 1 := by
            calc
              a = Nat.pred a + 1 := by
                symm
                exact Nat.succ_pred_eq_of_pos ha_pos
              _ = m + 1 := by rw [hpred]
          refine ⟨a, ?_, haΛ⟩
          simp [bidirectionalViewClause, haeq]
      · rcases Finset.mem_union.mp hrest with hbackwardOut | hbackwardIn
        · rcases Finset.mem_image.mp hbackwardOut with ⟨n, hnΛ, rfl⟩
          refine ⟨n, ?_, hnΛ⟩
          simp [bidirectionalViewClause]
        · rcases Finset.mem_image.mp hbackwardIn with ⟨m, hm, rfl⟩
          rcases Finset.mem_image.mp hm with ⟨a, haΛ, hpred⟩
          by_cases hzero : a = 0
          · subst hzero
            have hm0 : m = 0 := by simpa using hpred.symm
            subst hm0
            refine ⟨0, ?_, by simpa using haΛ⟩
            simp [bidirectionalViewClause]
          · have ha_pos : 0 < a := Nat.pos_of_ne_zero hzero
            have haeq : a = m + 1 := by
              calc
                a = Nat.pred a + 1 := by
                  symm
                  exact Nat.succ_pred_eq_of_pos ha_pos
                _ = m + 1 := by rw [hpred]
            refine ⟨a, ?_, haΛ⟩
            simp [bidirectionalViewClause, haeq]

theorem bidirectionalViewRegionSupport_complete
    {Λ : Region Nat} {j : BidirectionalViewClauseId}
    (hj : clauseTouchesRegion (bidirectionalViewClause j) Λ) :
    j ∈ bidirectionalViewRegionSupport Λ := by
  rcases j with n | m | m
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = n := by
      simpa [bidirectionalViewClause] using haAtoms
    subst a
    rw [bidirectionalViewRegionSupport]
    exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_image.mpr ⟨n, haΛ, rfl⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = m ∨ a = m + 1 := by
      simpa [bidirectionalViewClause] using haAtoms
    rw [bidirectionalViewRegionSupport]
    rcases ha with haEq | haNext
    · have hmΛ : m ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨m, hmΛ, rfl⟩
    · have hpredmem : Nat.pred a ∈ Finset.image Nat.pred Λ :=
        Finset.mem_image.mpr ⟨a, haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_image.mpr ⟨Nat.pred a, hpredmem, by simp [haNext]⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = m ∨ a = m + 1 := by
      simpa [bidirectionalViewClause] using haAtoms
    rw [bidirectionalViewRegionSupport]
    rcases ha with haEq | haNext
    · have hmΛ : m ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_image.mpr ⟨m, hmΛ, rfl⟩
    · have hpredmem : Nat.pred a ∈ Finset.image Nat.pred Λ :=
        Finset.mem_image.mpr ⟨a, haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_image.mpr ⟨Nat.pred a, hpredmem, by simp [haNext]⟩

/-- Bidirectional world-of-views specification: one prior weight per agent and
two local trust weights per adjacent pair. -/
noncomputable def bidirectionalWorldOfViewsClassicalSpec
    (bias forwardTrust backwardTrust : Nat → ℝ) :
    ClassicalInfiniteGroundMLNSpec Nat BidirectionalViewClauseId where
  clause := bidirectionalViewClause
  logWeight j := match j with
    | .prior n => bias n
    | .forward n => forwardTrust n
    | .backward n => backwardTrust n
  regionSupport := bidirectionalViewRegionSupport
  regionSupport_sound := fun hj => bidirectionalViewRegionSupport_sound hj
  regionSupport_complete := fun hj => bidirectionalViewRegionSupport_complete hj

/-- Uniform Dobrushin condition for bidirectional local trust.

If every agent's local row sum
`(|forwardTrust n| + |forwardTrust (pred n)| + |backwardTrust n| +
  |backwardTrust (pred n)|) / 2`
is bounded by the same `C < 1`, then the bidirectional world-of-views MLN
satisfies `PaperUniformSmallTotalInfluence`. -/
theorem bidirectionalWorldOfViewsClassicalSpec_uniformSmallTotalInfluence
    {bias forwardTrust backwardTrust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat,
          (|forwardTrust n| + |forwardTrust (Nat.pred n)| +
              |backwardTrust n| + |backwardTrust (Nat.pred n)|) / 2 ≤ C) :
    (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).PaperUniformSmallTotalInfluence := by
  rcases htrust with ⟨C, hC_nonneg, hC_lt_one, hrowBound⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro a
  let M := bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust
  have hsupp :
      M.regionSupport ({a} : Finset Nat) =
        ({BidirectionalViewClauseId.prior a,
          BidirectionalViewClauseId.forward a,
          BidirectionalViewClauseId.forward (Nat.pred a),
          BidirectionalViewClauseId.backward a,
          BidirectionalViewClauseId.backward (Nat.pred a)} :
            Finset BidirectionalViewClauseId) := by
    ext j
    simp [M, bidirectionalWorldOfViewsClassicalSpec, bidirectionalViewRegionSupport]
    tauto
  have hrow :
      Finset.sum (M.atomInteractionNeighborhood a)
          (fun b => M.pairwiseDobrushinCoefficient a b) =
        (1 / 2 : ℝ) * M.atomTotalInfluence a := by
    rw [M.atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  have hprior_zero :
      M.clauseInfluenceContribution (BidirectionalViewClauseId.prior a) = 0 := by
    apply M.clauseInfluenceContribution_eq_zero_of_card_le_one
    simp [M, bidirectionalWorldOfViewsClassicalSpec, bidirectionalViewClause,
      bidirectionalViewPriorClause_atoms]
  by_cases ha : a = 0
  · subst ha
    have htot0 :
        M.atomTotalInfluence 0 =
          |forwardTrust 0| + |backwardTrust 0| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        M, bidirectionalWorldOfViewsClassicalSpec, bidirectionalViewClause,
        bidirectionalViewForwardClause_atoms, bidirectionalViewBackwardClause_atoms]
    rw [htot0]
    have hbound0 : |forwardTrust 0| + |backwardTrust 0| ≤ C := by
      have h0 :
          (|forwardTrust 0| + |forwardTrust 0| + |backwardTrust 0| + |backwardTrust 0|) / 2 ≤ C := by
        simpa using hrowBound 0
      nlinarith [abs_nonneg (forwardTrust 0), abs_nonneg (backwardTrust 0), h0]
    nlinarith [abs_nonneg (forwardTrust 0), abs_nonneg (backwardTrust 0)]
  · have hpred_ne : Nat.pred a ≠ a := by
      exact Nat.ne_of_lt (Nat.pred_lt ha)
    have hnpred : a ≠ Nat.pred a := by
      intro h
      exact hpred_ne h.symm
    have hnpred_sub : a ≠ a - 1 := by
      simpa [Nat.pred_eq_sub_one] using hnpred
    have hsuminfl :
        ({BidirectionalViewClauseId.forward a,
          BidirectionalViewClauseId.forward (Nat.pred a),
          BidirectionalViewClauseId.backward a,
          BidirectionalViewClauseId.backward (Nat.pred a)} :
            Finset BidirectionalViewClauseId).sum
          (fun j => M.clauseInfluenceContribution j) =
          |forwardTrust a| + |forwardTrust (Nat.pred a)| +
            |backwardTrust a| + |backwardTrust (Nat.pred a)| := by
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_insert]
          · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
              M, bidirectionalWorldOfViewsClassicalSpec, bidirectionalViewClause, add_assoc]
          · simp [hnpred_sub]
        · simp
      · simp [hnpred_sub]
    have htot :
        M.atomTotalInfluence a =
          |forwardTrust a| + |forwardTrust (Nat.pred a)| +
            |backwardTrust a| + |backwardTrust (Nat.pred a)| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, hsuminfl]
      · simp
    rw [htot]
    nlinarith [hrowBound a,
      abs_nonneg (forwardTrust a), abs_nonneg (forwardTrust (Nat.pred a)),
      abs_nonneg (backwardTrust a), abs_nonneg (backwardTrust (Nat.pred a))]

/-- Existence for the bidirectional world-of-views MLN. -/
theorem exists_bidirectionalWorldOfViews_fixedRegionCylinderDLR
    (bias forwardTrust backwardTrust : Nat → ℝ) (ξ : BoundaryCondition Nat) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).exists_fixedRegionCylinderDLR_of_equiv
      beliefLineExhaustion ξ (Equiv.refl Nat)

/-- End-to-end uniqueness for bidirectional world-of-views models. -/
theorem bidirectionalWorldOfViews_uniqueMeasure
    {bias forwardTrust backwardTrust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat,
          (|forwardTrust n| + |forwardTrust (Nat.pred n)| +
              |backwardTrust n| + |backwardTrust (Nat.pred n)|) / 2 ≤ C) :
    (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).PaperUniqueMeasure :=
  (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (bidirectionalWorldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)

/-- The WM bridge is specification-determined under the same bidirectional
trust-budget hypothesis. -/
theorem bidirectionalWorldOfViews_wmBridge_unique
    {bias forwardTrust backwardTrust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat,
          (|forwardTrust n| + |forwardTrust (Nat.pred n)| +
              |backwardTrust n| + |backwardTrust (Nat.pred n)|) / 2 ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (q : ConstraintQuery Nat) :
    (infiniteMLNMassSemantics
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust)
      μ hμ).queryProb q =
    (infiniteMLNMassSemantics
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust)
      ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust)
    (bidirectionalWorldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)
    μ ν hμ hν q

/-- Quantitative local boundary-insensitivity for bidirectional world-of-views
queries. -/
theorem bidirectionalWorldOfViews_localQueryDiscrepancy_le_geometric
    {bias forwardTrust backwardTrust : Nat → ℝ}
    (htrust :
      ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
        ∀ n : Nat,
          (|forwardTrust n| + |forwardTrust (Nat.pred n)| +
              |backwardTrust n| + |backwardTrust (Nat.pred n)|) / 2 ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (Δ : Region Nat)
    (q : LocalConstraintQuery Nat Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := bidirectionalWorldOfViewsClassicalSpec bias forwardTrust backwardTrust)
    (bidirectionalWorldOfViewsClassicalSpec_uniformSmallTotalInfluence htrust)
    μ ν hμ hν Δ q

end Mettapedia.Logic.MarkovLogicInfiniteBidirectionalWorldOfViews
