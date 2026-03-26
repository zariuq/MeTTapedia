import Mathlib.Logic.Equiv.Nat
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel
import Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample

/-!
# Variable-Neighborhood World of Views

Agents on an **arbitrary countable bounded-degree interaction graph**, not
just a chain.  Each agent has an agent-specific finite set of neighbors,
and each directed edge carries its own trust weight.

The core structure `VarNeighborhoodSpec` takes:
- `nbrs a` : the agents who influence `a` (finite per agent);
- `reverseNbrs b` : the agents whom `b` influences (finite per agent);
- `tw a b` : directed trust weight (b → a);
- `pw a` : prior weight at `a`.

The uniform Dobrushin budget is the sum of incoming and outgoing local
trust contributions:
`∀ a, Σ_{b ∈ nbrs a} (1/2)|tw a b| + Σ_{c ∈ reverseNbrs a} (1/2)|tw c a| ≤ C < 1`.

This subsumes all chain-based examples as special cases.

**Positive example.**  A social network where each agent trusts at most 5
others, with pairwise trust ≤ 0.15 each, has budget ≤ 0.75 < 1 and admits
a unique global belief equilibrium.

**Negative example.**  A hub agent receiving strong trust from thousands
may push the incoming budget past 1.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteBeliefLineExample

/-- Clause ids for a variable-neighborhood graph on `Nat`. -/
inductive VarNClauseId where
  | prior : Nat → VarNClauseId
  | influence : Nat → Nat → VarNClauseId  -- influence a b = "b influences a"
deriving DecidableEq

def varNPriorClause (n : Nat) : GroundClause Nat := {Literal.pos n}

def varNInfluenceClause (a b : Nat) : GroundClause Nat :=
  {Literal.neg b, Literal.pos a}

def varNClause : VarNClauseId → GroundClause Nat
  | .prior n => varNPriorClause n
  | .influence a b => varNInfluenceClause a b

@[simp] theorem varNPriorClause_atoms (n : Nat) :
    (varNPriorClause n).atoms = {n} := by
  ext a; simp [varNPriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem varNInfluenceClause_atoms (a b : Nat) :
    (varNInfluenceClause a b).atoms = {b, a} := by
  ext x; simp [varNInfluenceClause, GroundClause.atoms, Literal.atom]

/-- Region support for the variable-neighborhood MLN.

    For a region Λ, the touching clauses are:
    - priors on atoms in Λ;
    - influence a b when a ∈ Λ (a is the target, influenced by b);
    - influence a b when b ∈ Λ (b is in the region, influencing a).

    We need `reverseNbrs b` = {a | b ∈ nbrs a} to enumerate the third case
    without requiring `Fintype Nat`. -/
noncomputable def varNRegionSupport
    (nbrs : Nat → Finset Nat)
    (reverseNbrs : Nat → Finset Nat)
    (Λ : Region Nat) : Finset VarNClauseId :=
  -- priors on atoms in Λ
  (Λ.image VarNClauseId.prior) ∪
  -- influence a b where a ∈ Λ (a is the influenced target)
  (Λ.biUnion fun a => (nbrs a).image fun b => VarNClauseId.influence a b) ∪
  -- influence a b where b ∈ Λ (b is in the region, a is the target outside)
  (Λ.biUnion fun b => (reverseNbrs b).image fun a => VarNClauseId.influence a b)

/-- The clause function gated by the neighborhood relation.
    Non-neighbor `influence a b` clauses map to the empty clause (no atoms),
    so they never touch any region and `regionSupport_complete` holds. -/
def varNClauseGated (nbrs : Nat → Finset Nat) : VarNClauseId → GroundClause Nat
  | .prior n => varNPriorClause n
  | .influence a b => if b ∈ nbrs a then varNInfluenceClause a b else ∅

theorem varNRegionSupport_sound
    (nbrs reverseNbrs : Nat → Finset Nat)
    (hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b)
    {Λ : Region Nat} {j : VarNClauseId}
    (hj : j ∈ varNRegionSupport nbrs reverseNbrs Λ) :
    clauseTouchesRegion (varNClauseGated nbrs j) Λ := by
  rw [varNRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hleft | hsource
  · rcases Finset.mem_union.mp hleft with hprior | htarget
    · rcases Finset.mem_image.mp hprior with ⟨n, hnΛ, rfl⟩
      refine ⟨n, ?_, hnΛ⟩
      simp [varNClauseGated]
    · rcases Finset.mem_biUnion.mp htarget with ⟨a, haΛ, hinfl⟩
      rcases Finset.mem_image.mp hinfl with ⟨b, hbNbr, rfl⟩
      refine ⟨a, ?_, haΛ⟩
      simp [varNClauseGated, hbNbr]
  · rcases Finset.mem_biUnion.mp hsource with ⟨b, hbΛ, hinfl⟩
    rcases Finset.mem_image.mp hinfl with ⟨a, haRev, rfl⟩
    have hbNbr : b ∈ nbrs a := (hrev a b).mpr haRev
    refine ⟨b, ?_, hbΛ⟩
    simp [varNClauseGated, hbNbr, varNInfluenceClause_atoms]

theorem varNRegionSupport_complete
    (nbrs reverseNbrs : Nat → Finset Nat)
    (hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b)
    {Λ : Region Nat} {j : VarNClauseId}
    (hj : clauseTouchesRegion (varNClauseGated nbrs j) Λ) :
    j ∈ varNRegionSupport nbrs reverseNbrs Λ := by
  cases j with
  | prior n =>
      simpa [varNRegionSupport, clauseTouchesRegion, varNClauseGated]
        using hj
  | influence a b =>
      by_cases hbNbr : b ∈ nbrs a
      · have htouch : clauseTouchesRegion (varNInfluenceClause a b) Λ := by
          simpa [varNClauseGated, hbNbr] using hj
        rcases htouch with ⟨x, hxAtoms, hxΛ⟩
        have hx : x = b ∨ x = a := by
          simpa [varNInfluenceClause_atoms, or_comm] using hxAtoms
        cases hx with
        | inl hxb =>
            have haRev : a ∈ reverseNbrs b := (hrev a b).mp hbNbr
            unfold varNRegionSupport
            exact Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_biUnion.mpr ⟨b, by simpa [hxb] using hxΛ,
                Finset.mem_image.mpr ⟨a, haRev, rfl⟩⟩
        | inr hxa =>
            unfold varNRegionSupport
            exact Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_union.mpr <| Or.inr <|
                Finset.mem_biUnion.mpr ⟨a, by simpa [hxa] using hxΛ,
                  Finset.mem_image.mpr ⟨b, hbNbr, rfl⟩⟩
      · exfalso
        rcases hj with ⟨x, hxAtoms, _⟩
        simp [varNClauseGated, hbNbr, GroundClause.atoms] at hxAtoms

/-- The variable-neighborhood classical infinite MLN.

    Requires `reverseNbrs` to be consistent: `b ∈ nbrs a ↔ a ∈ reverseNbrs b`.
    Non-neighbor influence clauses are gated to the empty clause, so they
    have no atoms and never appear in `regionSupport`. -/
noncomputable def varNeighborhoodSpec
    (nbrs reverseNbrs : Nat → Finset Nat)
    (hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b)
    (tw : Nat → Nat → ℝ)
    (pw : Nat → ℝ) :
    ClassicalInfiniteGroundMLNSpec Nat VarNClauseId where
  clause := varNClauseGated nbrs
  logWeight j := match j with
    | .prior n => pw n
    | .influence a b => tw a b
  regionSupport := varNRegionSupport nbrs reverseNbrs
  regionSupport_sound := by
    intro Λ j hj
    exact varNRegionSupport_sound nbrs reverseNbrs hrev hj
  regionSupport_complete := by
    intro Λ j hj
    exact varNRegionSupport_complete nbrs reverseNbrs hrev hj

/-- Initial-segment exhaustion of `Nat` reused for variable-neighborhood worlds
of views. -/
def varNeighborhoodExhaustion : RegionExhaustion Nat := beliefLineExhaustion

/-- Existence for the variable-neighborhood MLN. -/
theorem exists_varNeighborhood_fixedRegionCylinderDLR
    (nbrs reverseNbrs : Nat → Finset Nat)
    (hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b)
    (tw : Nat → Nat → ℝ) (pw : Nat → ℝ)
    (ξ : BoundaryCondition Nat) :
    ∃ μ : Measure (InfiniteWorld Nat),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).toStrictlyPositiveInfiniteGroundMLNSpec
          μ := by
  simpa using
    (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).exists_fixedRegionCylinderDLR_of_equiv
      varNeighborhoodExhaustion ξ (Equiv.refl Nat)

/-- Uniform Dobrushin condition for variable-neighborhood trust. -/
theorem varNeighborhoodSpec_uniformSmallTotalInfluence
    {nbrs reverseNbrs : Nat → Finset Nat}
    {hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b}
    {tw : Nat → Nat → ℝ} {pw : Nat → ℝ}
    (hbudget : ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ a,
        (nbrs a).sum (fun b => (1 / 2 : ℝ) * |tw a b|) +
          (reverseNbrs a).sum (fun c => (1 / 2 : ℝ) * |tw c a|) ≤ C) :
    (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).PaperUniformSmallTotalInfluence := by
  classical
  rcases hbudget with ⟨C, hC_nonneg, hC_lt_one, hrowBound⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro a
  let M := varNeighborhoodSpec nbrs reverseNbrs hrev tw pw
  let incoming : Finset VarNClauseId := (nbrs a).image fun b => VarNClauseId.influence a b
  let outgoing : Finset VarNClauseId := (reverseNbrs a).image fun c => VarNClauseId.influence c a
  have hsupp :
      M.regionSupport ({a} : Finset Nat) =
        ({VarNClauseId.prior a} ∪ incoming ∪ outgoing) := by
    ext j
    simp [M, incoming, outgoing, varNeighborhoodSpec, varNRegionSupport]
  have hrow :
      Finset.sum (M.atomInteractionNeighborhood a)
        (fun b => M.pairwiseDobrushinCoefficient a b) =
        (1 / 2 : ℝ) * M.atomTotalInfluence a := by
    rw [M.atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  have hprior_zero :
      M.clauseInfluenceContribution (VarNClauseId.prior a) = 0 := by
    apply M.clauseInfluenceContribution_eq_zero_of_card_le_one
    simp [M, varNeighborhoodSpec, varNClauseGated, varNPriorClause_atoms]
  have hincoming_bound :
      incoming.sum (fun j => M.clauseInfluenceContribution j) ≤
        (nbrs a).sum (fun b => |tw a b|) := by
    dsimp [incoming]
    rw [Finset.sum_image]
    · refine Finset.sum_le_sum ?_
      intro b hb
      by_cases hab : b = a
      · subst hab
        simp [M, varNeighborhoodSpec, varNClauseGated, hb,
          ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          varNInfluenceClause_atoms]
      · simp [M, varNeighborhoodSpec, varNClauseGated, hb, hab,
          ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          varNInfluenceClause_atoms]
    · intro x hx y hy hxy
      injection hxy
  have houtgoing_bound :
      outgoing.sum (fun j => M.clauseInfluenceContribution j) ≤
        (reverseNbrs a).sum (fun c => |tw c a|) := by
    dsimp [outgoing]
    rw [Finset.sum_image]
    · refine Finset.sum_le_sum ?_
      intro src hsrc
      by_cases hself : src = a
      · subst src
        have hNbr : a ∈ nbrs a := (hrev a a).mpr hsrc
        have hEq :
            M.clauseInfluenceContribution (VarNClauseId.influence a a) = 0 := by
          apply M.clauseInfluenceContribution_eq_zero_of_card_le_one
          simp [M, varNeighborhoodSpec, varNClauseGated, hNbr, varNInfluenceClause_atoms]
        rw [hEq]
        exact abs_nonneg _
      · have hNbr : a ∈ nbrs src := (hrev src a).mpr hsrc
        have hEq :
            M.clauseInfluenceContribution (VarNClauseId.influence src a) = |tw src a| := by
          have hneq : a ≠ src := by
            intro h
            exact hself h.symm
          have hcard :
              (((M.clause (VarNClauseId.influence src a)).atoms.card - 1 : Nat) : ℝ) = 1 := by
            simp [M, varNeighborhoodSpec, varNClauseGated, hNbr, varNInfluenceClause_atoms, hneq]
          unfold ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution
          rw [hcard]
          simp [M, varNeighborhoodSpec]
        rw [hEq]
    · intro x hx y hy hxy
      injection hxy
  have hsum_union_le :
      ∀ s t : Finset VarNClauseId,
        (s ∪ t).sum (fun j => M.clauseInfluenceContribution j) ≤
          s.sum (fun j => M.clauseInfluenceContribution j) +
            t.sum (fun j => M.clauseInfluenceContribution j) := by
    intro s t
    rw [← Finset.union_sdiff_of_subset (s := s) (t := s ∪ t) (by exact Finset.subset_union_left)]
    rw [Finset.sum_union]
    · have hsubset : (s ∪ t) \ s ⊆ t := by
        intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxUnion, hxNotMem⟩
        rcases Finset.mem_union.mp hxUnion with hxS | hxT
        · exact False.elim (hxNotMem hxS)
        · exact hxT
      have hle :
          ((s ∪ t) \ s).sum (fun j => M.clauseInfluenceContribution j) ≤
            t.sum (fun j => M.clauseInfluenceContribution j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by intro x hx _; exact M.clauseInfluenceContribution_nonneg x)
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hle
        (s.sum (fun j => M.clauseInfluenceContribution j))
    · exact Finset.disjoint_sdiff
  calc
    Finset.sum (M.atomInteractionNeighborhood a)
        (fun b => M.pairwiseDobrushinCoefficient a b)
      = (1 / 2 : ℝ) * M.atomTotalInfluence a := hrow
    _ = (1 / 2 : ℝ) *
        (({VarNClauseId.prior a} ∪ incoming ∪ outgoing).sum
          (fun j => M.clauseInfluenceContribution j)) := by
          rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp]
    _ ≤ (1 / 2 : ℝ) *
        ((({VarNClauseId.prior a} ∪ incoming).sum
            (fun j => M.clauseInfluenceContribution j)) +
          outgoing.sum (fun j => M.clauseInfluenceContribution j)) := by
          gcongr
          exact hsum_union_le ({VarNClauseId.prior a} ∪ incoming) outgoing
    _ ≤ (1 / 2 : ℝ) *
        (((( {VarNClauseId.prior a} : Finset VarNClauseId).sum
              (fun j => M.clauseInfluenceContribution j)) +
            incoming.sum (fun j => M.clauseInfluenceContribution j)) +
          outgoing.sum (fun j => M.clauseInfluenceContribution j)) := by
          gcongr
          exact hsum_union_le ({VarNClauseId.prior a} : Finset VarNClauseId) incoming
    _ = (1 / 2 : ℝ) *
        (incoming.sum (fun j => M.clauseInfluenceContribution j) +
          outgoing.sum (fun j => M.clauseInfluenceContribution j)) := by
          simp [hprior_zero]
    _ ≤ (1 / 2 : ℝ) *
        ((nbrs a).sum (fun b => |tw a b|) +
          (reverseNbrs a).sum (fun c => |tw c a|)) := by
          gcongr
    _ = (nbrs a).sum (fun b => (1 / 2 : ℝ) * |tw a b|) +
          (reverseNbrs a).sum (fun c => (1 / 2 : ℝ) * |tw c a|) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C := hrowBound a

/-- End-to-end uniqueness for variable-neighborhood worlds of views. -/
theorem varNeighborhood_uniqueMeasure
    {nbrs reverseNbrs : Nat → Finset Nat}
    {hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b}
    {tw : Nat → Nat → ℝ} {pw : Nat → ℝ}
    (hbudget : ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ a,
        (nbrs a).sum (fun b => (1 / 2 : ℝ) * |tw a b|) +
          (reverseNbrs a).sum (fun c => (1 / 2 : ℝ) * |tw c a|) ≤ C) :
    (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).PaperUniqueMeasure :=
  (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (varNeighborhoodSpec_uniformSmallTotalInfluence hbudget)

/-- End-to-end WM bridge for variable-neighborhood worlds of views. -/
theorem varNeighborhood_wmBridge_unique
    {nbrs reverseNbrs : Nat → Finset Nat}
    {hrev : ∀ a b, b ∈ nbrs a ↔ a ∈ reverseNbrs b}
    {tw : Nat → Nat → ℝ} {pw : Nat → ℝ}
    (hbudget : ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ a,
        (nbrs a).sum (fun b => (1 / 2 : ℝ) * |tw a b|) +
          (reverseNbrs a).sum (fun c => (1 / 2 : ℝ) * |tw c a|) ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ : FixedRegionCylinderDLR
      (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Nat)))
    (hν : FixedRegionCylinderDLR
      (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Nat)))
    (q : ConstraintQuery Nat) :
    (infiniteMLNMassSemantics (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (varNeighborhoodSpec nbrs reverseNbrs hrev tw pw)
    (varNeighborhoodSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν q

end Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
