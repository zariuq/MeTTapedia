import Mettapedia.Logic.MarkovLogicInfiniteExistence
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-!
# Infinite Belief-Line MLN Example

An unbounded chain of agents indexed by `Nat`, each holding a Boolean belief.

- `prior n` softly biases agent `n` toward believing;
- `influence n` couples agents `n` and `n+1` via `{neg n, pos (n+1)}`.

The clause creates **bidirectional** statistical coupling at the Dobrushin
level: flipping either agent's truth value shifts the other's conditional
probability.  The logical "implication" direction does not restrict the
interaction — both agents influence each other.

The parametric classical version (`beliefLineClassicalSpec w`) lets the
influence weight vary.  When `|w| < 1`, the Dobrushin row sum is uniformly
bounded by `|w|`, giving a unique global Gibbs semantics and a
specification-determined WM query strength for every finite query.

**Positive example.**  `w = 0.4` (odds multiplier `e^0.4 ≈ 1.49`).  Budget
`0.4 < 1`.  Belief probabilities are uniquely determined.

**Negative example.**  `w = log 3 ≈ 1.1`.  Budget exceeds 1.  Existence still
holds, but the proved uniqueness theorem does not apply.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteExistence
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteExistence.RegionExhaustion

/-- Clause ids for the countable belief-line MLN. -/
inductive BeliefClauseId where
  | prior : Nat → BeliefClauseId
  | influence : Nat → BeliefClauseId
deriving DecidableEq

/-- Soft bias toward believing at site `n`. -/
def beliefLinePriorClause (n : Nat) : GroundClause Nat :=
  {Literal.pos n}

/-- Neighbor influence: if `n` believes, site `n + 1` is nudged to believe too. -/
def beliefLineInfluenceClause (n : Nat) : GroundClause Nat :=
  {Literal.neg n, Literal.pos (n + 1)}

/-- The classical clause underlying a given belief-line id. -/
def beliefLineClause : BeliefClauseId → GroundClause Nat
  | .prior n => beliefLinePriorClause n
  | .influence n => beliefLineInfluenceClause n

@[simp] theorem beliefLinePriorClause_atoms (n : Nat) :
    (beliefLinePriorClause n).atoms = ({n} : Finset Nat) := by
  ext a
  simp [beliefLinePriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem beliefLineInfluenceClause_atoms (n : Nat) :
    (beliefLineInfluenceClause n).atoms = ({n, n + 1} : Finset Nat) := by
  ext a
  simp [beliefLineInfluenceClause, GroundClause.atoms, Literal.atom]

/-- Prior belief weight: satisfying the prior doubles the local factor. -/
noncomputable def priorLogWeight : ℝ := Real.log 2

/-- Influence weight: satisfying the edge clause triples the local factor. -/
noncomputable def influenceLogWeight : ℝ := Real.log 3

/-- The weighted clause attached to a belief-line id. -/
noncomputable def beliefLineWeightedClause (j : BeliefClauseId) : WeightedGroundClause Nat :=
  classicalWeightedClause (beliefLineClause j)
    (match j with
    | .prior _ => priorLogWeight
    | .influence _ => influenceLogWeight)

/-- Finite clause support for a finite set of agents:
priors on the region, outgoing influence edges, and incoming influence edges. -/
noncomputable def beliefLineRegionSupport (Λ : Region Nat) : Finset BeliefClauseId :=
  (Λ.image BeliefClauseId.prior) ∪
    ((Λ.image BeliefClauseId.influence) ∪
      ((Λ.image Nat.pred).image BeliefClauseId.influence))

theorem beliefLineRegionSupport_sound
    {Λ : Region Nat} {j : BeliefClauseId}
    (hj : j ∈ beliefLineRegionSupport Λ) :
    clauseTouchesRegion (beliefLineClause j) Λ := by
  rw [beliefLineRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hprior | hrest
  · rcases Finset.mem_image.mp hprior with ⟨n, hnΛ, rfl⟩
    refine ⟨n, ?_, hnΛ⟩
    simp [beliefLineClause]
  · rcases Finset.mem_union.mp hrest with hout | hin
    · rcases Finset.mem_image.mp hout with ⟨n, hnΛ, rfl⟩
      refine ⟨n, ?_, hnΛ⟩
      simp [beliefLineClause]
    · rcases Finset.mem_image.mp hin with ⟨m, hm, rfl⟩
      rcases Finset.mem_image.mp hm with ⟨a, haΛ, hpred⟩
      by_cases hzero : a = 0
      · subst hzero
        have hm0 : m = 0 := by simpa using hpred.symm
        subst hm0
        refine ⟨0, ?_, by simpa using haΛ⟩
        simp [beliefLineClause]
      · have ha_pos : 0 < a := Nat.pos_of_ne_zero hzero
        have haeq : a = m + 1 := by
          calc
            a = Nat.pred a + 1 := by
              symm
              exact Nat.succ_pred_eq_of_pos ha_pos
            _ = m + 1 := by rw [hpred]
        refine ⟨a, ?_, haΛ⟩
        simp [beliefLineClause, haeq]

theorem beliefLineRegionSupport_complete
    {Λ : Region Nat} {j : BeliefClauseId}
    (hj : clauseTouchesRegion (beliefLineClause j) Λ) :
    j ∈ beliefLineRegionSupport Λ := by
  rcases j with n | m
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = n := by
      simpa [beliefLineClause] using haAtoms
    subst a
    rw [beliefLineRegionSupport]
    exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_image.mpr ⟨n, haΛ, rfl⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = m ∨ a = m + 1 := by
      simpa [beliefLineClause] using haAtoms
    rw [beliefLineRegionSupport]
    rcases ha with haEq | haNext
    · have hmΛ : m ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨m, hmΛ, rfl⟩
    · have hpredmem : Nat.pred a ∈ Finset.image Nat.pred Λ :=
        Finset.mem_image.mpr ⟨a, haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_image.mpr ⟨Nat.pred a, hpredmem, by simp [haNext]⟩

/-- The strictly positive infinite MLN for the belief line. -/
noncomputable def beliefLineSpec :
    StrictlyPositiveInfiniteGroundMLNSpec Nat BeliefClauseId where
  clauseData := beliefLineWeightedClause
  regionSupport := beliefLineRegionSupport
  regionSupport_sound := by
    intro Λ j hj
    exact beliefLineRegionSupport_sound hj
  regionSupport_complete := by
    intro Λ j hj
    exact beliefLineRegionSupport_complete hj
  satisfiedPotential_ne_zero := by
    intro j
    simpa [beliefLineWeightedClause] using
      classicalWeightedClause_satisfiedPotential_ne_zero
        (clause := beliefLineClause j)
        (logWeight := match j with
          | .prior _ => priorLogWeight
          | .influence _ => influenceLogWeight)
  unsatisfiedPotential_ne_zero := by
    intro j
    simpa [beliefLineWeightedClause] using
      classicalWeightedClause_unsatisfiedPotential_ne_zero
        (clause := beliefLineClause j)
        (logWeight := match j with
          | .prior _ => priorLogWeight
          | .influence _ => influenceLogWeight)

/-- Initial-segment exhaustion of the countable agent line. -/
def beliefLineExhaustion : RegionExhaustion Nat where
  region n := Finset.range (n + 1)
  monotone := by
    intro m n hmn a ha
    exact Finset.mem_range.mpr <|
      lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_succ hmn)
  exhaustive := by
    intro a
    exact ⟨a, Finset.mem_range.mpr (Nat.lt_succ_self a)⟩

/-- The singleton event that agent `n` believes. -/
def believesHereAssignments (n : Nat) :
    Set (LocalAssignment Nat ({n} : Region Nat)) :=
  {x | x ⟨n, by simp⟩ = true}

theorem measurableSet_believesHereAssignments (n : Nat) :
    MeasurableSet (believesHereAssignments n) := by
  classical
  exact MeasurableSet.of_discrete

/-- The local neighborhood used to resample belief around site `n`. -/
def beliefNeighborhood (n : Nat) : Region Nat := ({n, n + 1} : Finset Nat)

/-- Global fixed-region DLR for the belief-line example under a marginal cluster
point hypothesis. -/
theorem beliefLine_fixedRegionCylinderDLR
    {ξ : BoundaryCondition Nat}
    {μ : Measure (InfiniteWorld Nat)}
    [IsProbabilityMeasure μ]
    (h : MarginalClusterPoint beliefLineExhaustion beliefLineSpec ξ μ) :
    FixedRegionCylinderDLR beliefLineSpec μ := by
  exact MarginalClusterPoint.fixedRegionCylinderDLR
    (E := beliefLineExhaustion) (M := beliefLineSpec) (ξ := ξ) (μ := μ) h

/-- Concrete motivating corollary:
averaging the local two-agent belief kernel around `n` preserves the global
probability that agent `n` believes. -/
theorem beliefLine_singleAgentBelief_fixedRegionDLR
    {ξ : BoundaryCondition Nat}
    {μ : Measure (InfiniteWorld Nat)}
    [IsProbabilityMeasure μ]
    (h : MarginalClusterPoint beliefLineExhaustion beliefLineSpec ξ μ)
    (n : Nat) :
    ∫⁻ ω,
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        beliefLineSpec (beliefNeighborhood n) ω
        (MeasureTheory.cylinder ({n} : Region Nat) (believesHereAssignments n))
      ∂ μ =
      μ (MeasureTheory.cylinder ({n} : Region Nat) (believesHereAssignments n)) := by
  exact
    beliefLine_fixedRegionCylinderDLR (μ := μ) (ξ := ξ) h
      (beliefNeighborhood n)
      ({n} : Region Nat)
      (believesHereAssignments n)
      (measurableSet_believesHereAssignments n)

/-- The belief-line MLN now inherits the paper-shaped existence theorem at the
current fixed-region cylinder DLR frontier. -/
theorem exists_beliefLine_fixedRegionCylinderDLR
    (ξ : BoundaryCondition Nat) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ, FixedRegionCylinderDLR beliefLineSpec μ := by
  simpa using
    (exists_fixedRegionCylinderDLR_of_equiv
      (E := beliefLineExhaustion)
      (M := beliefLineSpec)
      (ξ := ξ)
      (e := Equiv.refl Nat))

-- ═══════════════════════════════════════════════════════════════════════════
-- End-to-end example: existence + uniqueness + WM bridge
-- ═══════════════════════════════════════════════════════════════════════════

open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicClauseFactorGraph

/-- Classical belief-line MLN with parametric influence weight `w`.
    The prior weight is fixed at `log 2`; the influence weight is adjustable
    so that the Dobrushin condition can be satisfied by choosing `|w| < 1`.

    Positive example: `w = 0.4` gives influence factor `e^0.4 ≈ 1.49` —
    each neighbor multiplies belief odds by ~50%, with total incoming
    Dobrushin influence = 0.4 per agent, well within the budget.

    Negative example: `w = log 3 ≈ 1.1` exceeds the budget — the original
    `beliefLineSpec` weights. Existence still holds but uniqueness is not
    guaranteed. -/
noncomputable def beliefLineClassicalSpec (w : ℝ) :
    ClassicalInfiniteGroundMLNSpec Nat BeliefClauseId where
  clause := beliefLineClause
  logWeight j := match j with
    | .prior _ => priorLogWeight
    | .influence _ => w
  regionSupport := beliefLineRegionSupport
  regionSupport_sound := fun hj => beliefLineRegionSupport_sound hj
  regionSupport_complete := fun hj => beliefLineRegionSupport_complete hj

/-- The Dobrushin row sum for the belief line equals `|w|` for interior
    atoms and `(1/2)|w|` for atom 0.  Therefore `|w| < 1` suffices for
    `PaperUniformSmallTotalInfluence`. -/
theorem beliefLineClassicalSpec_uniformSmallTotalInfluence
    {w : ℝ} (hw : |w| < 1) :
    (beliefLineClassicalSpec w).PaperUniformSmallTotalInfluence := by
  refine ⟨|w|, abs_nonneg w, hw, ?_⟩
  intro a
  have hsupp :
      (beliefLineClassicalSpec w).regionSupport ({a} : Finset Nat) =
        ({BeliefClauseId.prior a, BeliefClauseId.influence a,
          BeliefClauseId.influence (Nat.pred a)} : Finset BeliefClauseId) := by
    ext j
    simp [beliefLineClassicalSpec, beliefLineRegionSupport]
    tauto
  have hrow :
      Finset.sum ((beliefLineClassicalSpec w).atomInteractionNeighborhood a)
        (fun b => (beliefLineClassicalSpec w).pairwiseDobrushinCoefficient a b) =
        (1 / 2 : ℝ) * (beliefLineClassicalSpec w).atomTotalInfluence a := by
    rw [(beliefLineClassicalSpec w).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  have hnonneg : 0 ≤ |w| := abs_nonneg w
  by_cases ha : a = 0
  · subst ha
    have htot0 :
        (beliefLineClassicalSpec w).atomTotalInfluence 0 = |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        beliefLineClassicalSpec, beliefLineClause, beliefLineInfluenceClause_atoms]
    rw [htot0]
    nlinarith
  · have hpred_ne : Nat.pred a ≠ a := by
      exact Nat.ne_of_lt (Nat.pred_lt ha)
    have hprior_zero :
        (beliefLineClassicalSpec w).clauseInfluenceContribution (BeliefClauseId.prior a) = 0 := by
      apply (beliefLineClassicalSpec w).clauseInfluenceContribution_eq_zero_of_card_le_one
      simp [beliefLineClassicalSpec, beliefLineClause, beliefLinePriorClause_atoms]
    have hsuminfl :
        ({BeliefClauseId.influence a, BeliefClauseId.influence (Nat.pred a)} :
            Finset BeliefClauseId).sum
          (fun j => (beliefLineClassicalSpec w).clauseInfluenceContribution j) =
          2 * |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          beliefLineClassicalSpec, beliefLineClause, beliefLineInfluenceClause_atoms]
        ring_nf
      · intro h
        injection h with hEq
        exact hpred_ne hEq.symm
    have htot :
        (beliefLineClassicalSpec w).atomTotalInfluence a = 2 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, hsuminfl]
      · simp
    rw [htot]
    nlinarith

/-- **End-to-end uniqueness**: for the belief line with `|w| < 1`,
    any two DLR measures agree on all finite-region marginals. -/
theorem beliefLine_uniqueMeasure
    {w : ℝ} (hw : |w| < 1) :
    (beliefLineClassicalSpec w).PaperUniqueMeasure :=
  (beliefLineClassicalSpec w).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (beliefLineClassicalSpec_uniformSmallTotalInfluence hw)

/-- **End-to-end WM bridge**: for the belief line with `|w| < 1`,
    the WM query strength is uniquely determined by the specification.
    Any two DLR measures yield the same `queryProb` for every finite query. -/
theorem beliefLine_wmBridge_unique
    {w : ℝ} (hw : |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (beliefLineClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (beliefLineClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (q : ConstraintQuery Nat) :
    (infiniteMLNMassSemantics (beliefLineClassicalSpec w) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (beliefLineClassicalSpec w) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (beliefLineClassicalSpec w)
    (beliefLineClassicalSpec_uniformSmallTotalInfluence hw)
    μ ν hμ hν q

end Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample
