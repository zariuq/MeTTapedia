import Mettapedia.Logic.PLNMarkovLogicInfiniteExistence

/-!
# Infinite Belief-Line MLN Example

This module gives a small motivating infinite-MLN example:

- atoms are indexed by `Nat`, representing an unbounded line of agents,
- `prior n` softly favors agent `n` holding the belief,
- `influence n` softly encodes `Believes n -> Believes (n+1)`.

Philosophically, this is a toy model of belief propagation in an open-ended
community.  It is a positive example of how infinite MLNs can describe stable
local belief laws in an unbounded social setting.

Negative example: this model says nothing about whether the belief is true.  It
only models relational reinforcement and global equilibrium of those local
influences.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteBeliefLineExample

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicClauseSemantics
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend
open Mettapedia.Logic.PLNMarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.PLNMarkovLogicInfiniteExistence
open Mettapedia.Logic.PLNMarkovLogicInfiniteClusterFrontend.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteFixedRegionDLR.RegionExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfiniteExistence.RegionExhaustion

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

end Mettapedia.Logic.PLNMarkovLogicInfiniteBeliefLineExample
