import Mathlib.Logic.Equiv.Nat
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-!
# Infinite 2D Grid MLN — the Ising Lattice in the Dobrushin Regime

The atom space is `Nat × Nat`: an unbounded rectangular lattice of Boolean
variables.  Each nearest-neighbour pair shares a weighted clause with log-weight
`w`.  A clause like `{neg (i,j), pos (i+1,j)}` couples the two nodes
**bidirectionally** at the Dobrushin level: flipping either node shifts the
other's conditional probability.  The logical "direction" of the clause
(implication) does not restrict the statistical coupling.

Each interior node has four interacting neighbours — two horizontal, two
vertical — giving a Dobrushin row sum of `2|w|`.  The uniqueness budget is
therefore `2|w| < 1`, or equivalently `|w| < 1/2`.

This is the formal 2D Ising model in the high-temperature (Dobrushin
uniqueness) regime — the most studied lattice model in statistical mechanics.

**Positive example.**  `w = 0.2` (odds multiplier `e^0.2 ≈ 1.22`).  Budget
`2 × 0.2 = 0.4 < 1`.  The probability at sensor `(15, 23)` is uniquely
determined, regardless of boundary conditions at infinity.

**Negative example.**  `w = 0.6`.  Budget `2 × 0.6 = 1.2 ≥ 1`.  This is the
low-temperature Ising regime: coexisting equilibria become possible and the
proved uniqueness theorem does not apply.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteGridExample

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

/-- Countable grid nodes. -/
abbrev GridNode := Nat × Nat

/-- Clause ids for the infinite 2D grid. -/
inductive GridClauseId where
  | prior : Nat → Nat → GridClauseId
  | horizontal : Nat → Nat → GridClauseId
  | vertical : Nat → Nat → GridClauseId
deriving DecidableEq

/-- Soft bias on a single grid node. -/
def gridPriorClause (i j : Nat) : GroundClause GridNode :=
  {Literal.pos (i, j)}

/-- Horizontal nearest-neighbour influence. -/
def gridHorizontalClause (i j : Nat) : GroundClause GridNode :=
  {Literal.neg (i, j), Literal.pos (i + 1, j)}

/-- Vertical nearest-neighbour influence. -/
def gridVerticalClause (i j : Nat) : GroundClause GridNode :=
  {Literal.neg (i, j), Literal.pos (i, j + 1)}

/-- Underlying clause attached to a grid clause id. -/
def gridClause : GridClauseId → GroundClause GridNode
  | .prior i j => gridPriorClause i j
  | .horizontal i j => gridHorizontalClause i j
  | .vertical i j => gridVerticalClause i j

@[simp] theorem gridPriorClause_atoms (i j : Nat) :
    (gridPriorClause i j).atoms = ({(i, j)} : Finset GridNode) := by
  ext a
  simp [gridPriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem gridHorizontalClause_atoms (i j : Nat) :
    (gridHorizontalClause i j).atoms = ({(i, j), (i + 1, j)} : Finset GridNode) := by
  ext a
  simp [gridHorizontalClause, GroundClause.atoms, Literal.atom]

@[simp] theorem gridVerticalClause_atoms (i j : Nat) :
    (gridVerticalClause i j).atoms = ({(i, j), (i, j + 1)} : Finset GridNode) := by
  ext a
  simp [gridVerticalClause, GroundClause.atoms, Literal.atom]

/-- Finite clause support for a finite grid region. -/
noncomputable def gridRegionSupport (Λ : Region GridNode) : Finset GridClauseId :=
  (Λ.image (fun p => GridClauseId.prior p.1 p.2)) ∪
    ((Λ.image (fun p => GridClauseId.horizontal p.1 p.2)) ∪
      (((Λ.image fun p => (Nat.pred p.1, p.2)).image
          (fun p => GridClauseId.horizontal p.1 p.2)) ∪
        ((Λ.image (fun p => GridClauseId.vertical p.1 p.2)) ∪
          (((Λ.image fun p => (p.1, Nat.pred p.2)).image
              (fun p => GridClauseId.vertical p.1 p.2))))))

theorem gridRegionSupport_sound
    {Λ : Region GridNode} {j : GridClauseId}
    (hj : j ∈ gridRegionSupport Λ) :
    clauseTouchesRegion (gridClause j) Λ := by
  rw [gridRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hprior | hrest
  · rcases Finset.mem_image.mp hprior with ⟨p, hpΛ, rfl⟩
    refine ⟨p, ?_, hpΛ⟩
    simp [gridClause]
  · rcases Finset.mem_union.mp hrest with hhorOut | hrest
    · rcases Finset.mem_image.mp hhorOut with ⟨p, hpΛ, rfl⟩
      refine ⟨p, ?_, hpΛ⟩
      simp [gridClause]
    · rcases Finset.mem_union.mp hrest with hhorIn | hrest
      · rcases Finset.mem_image.mp hhorIn with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
        by_cases hzero : a.1 = 0
        · rcases a with ⟨i, j⟩
          simp at hzero
          subst hzero
          have hp0 : p = (0, j) := by
            simpa using hpred.symm
          subst hp0
          refine ⟨(0, j), ?_, by simpa using haΛ⟩
          simp [gridClause]
        · rcases a with ⟨i, j⟩
          have hi_pos : 0 < i := Nat.pos_of_ne_zero hzero
          have hpEq : p = (Nat.pred i, j) := by
            simpa using hpred.symm
          subst hpEq
          refine ⟨(i, j), ?_, by simpa using haΛ⟩
          have hmem : (i, j) = (Nat.pred i + 1, j) := by
            exact congrArg (fun n => (n, j)) (Nat.succ_pred_eq_of_pos hi_pos).symm
          simpa [gridClause, gridHorizontalClause_atoms] using Or.inr hmem
      · rcases Finset.mem_union.mp hrest with hvertOut | hvertIn
        · rcases Finset.mem_image.mp hvertOut with ⟨p, hpΛ, rfl⟩
          refine ⟨p, ?_, hpΛ⟩
          simp [gridClause]
        · rcases Finset.mem_image.mp hvertIn with ⟨p, hp, rfl⟩
          rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
          by_cases hzero : a.2 = 0
          · rcases a with ⟨i, j⟩
            simp at hzero
            subst hzero
            have hp0 : p = (i, 0) := by
              simpa using hpred.symm
            subst hp0
            refine ⟨(i, 0), ?_, by simpa using haΛ⟩
            simp [gridClause]
          · rcases a with ⟨i, j⟩
            have hj_pos : 0 < j := Nat.pos_of_ne_zero hzero
            have hpEq : p = (i, Nat.pred j) := by
              simpa using hpred.symm
            subst hpEq
            refine ⟨(i, j), ?_, by simpa using haΛ⟩
            have hmem : (i, j) = (i, Nat.pred j + 1) := by
              exact congrArg (Prod.mk i) (Nat.succ_pred_eq_of_pos hj_pos).symm
            simpa [gridClause, gridVerticalClause_atoms] using Or.inr hmem

theorem gridRegionSupport_complete
    {Λ : Region GridNode} {j : GridClauseId}
    (hj : clauseTouchesRegion (gridClause j) Λ) :
    j ∈ gridRegionSupport Λ := by
  rcases j with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) := by
      simpa [gridClause] using haAtoms
    subst a
    rw [gridRegionSupport]
    exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_image.mpr ⟨(i, j), haΛ, rfl⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) ∨ a = (i + 1, j) := by
      simpa [gridClause] using haAtoms
    rw [gridRegionSupport]
    rcases ha with haEq | haNext
    · have hmem : (i, j) ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
    · have hpredmem : (Nat.pred (i + 1), j) ∈ Finset.image (fun p => (Nat.pred p.1, p.2)) Λ :=
        Finset.mem_image.mpr ⟨(i + 1, j), by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_image.mpr ⟨(Nat.pred (i + 1), j), hpredmem, by simp⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) ∨ a = (i, j + 1) := by
      simpa [gridClause] using haAtoms
    rw [gridRegionSupport]
    rcases ha with haEq | haNext
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_image.mpr ⟨(i, j), by simpa [haEq] using haΛ, rfl⟩
    · have hpredmem : (i, Nat.pred (j + 1)) ∈ Finset.image (fun p => (p.1, Nat.pred p.2)) Λ :=
        Finset.mem_image.mpr ⟨(i, j + 1), by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_image.mpr ⟨(i, Nat.pred (j + 1)), hpredmem, by simp⟩

/-- Square-box exhaustion of the countable grid. -/
def gridExhaustion : RegionExhaustion GridNode where
  region n := (Finset.range (n + 1)).product (Finset.range (n + 1))
  monotone := by
    intro m n hmn a ha
    rcases Finset.mem_product.mp ha with ⟨hi, hj⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_succ hmn),
       Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hmn)⟩
  exhaustive := by
    intro a
    rcases a with ⟨i, j⟩
    refine ⟨max i j, Finset.mem_product.mpr ?_⟩
    constructor
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_max_left i j) (Nat.lt_succ_self (max i j)))
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_max_right i j) (Nat.lt_succ_self (max i j)))

/-- Classical infinite MLN on the nearest-neighbour grid. -/
noncomputable def gridClassicalSpec (w : ℝ) :
    ClassicalInfiniteGroundMLNSpec GridNode GridClauseId where
  clause := gridClause
  logWeight j := match j with
    | .prior _ _ => Real.log 2
    | .horizontal _ _ => w
    | .vertical _ _ => w
  regionSupport := gridRegionSupport
  regionSupport_sound := fun hj => gridRegionSupport_sound hj
  regionSupport_complete := fun hj => gridRegionSupport_complete hj

/-- The 2D nearest-neighbour grid has Dobrushin row sum at most `2 * |w|`. -/
theorem gridClassicalSpec_uniformSmallTotalInfluence
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridClassicalSpec w).PaperUniformSmallTotalInfluence := by
  refine ⟨2 * |w|, by positivity, hbudget, ?_⟩
  intro a
  rcases a with ⟨i, j⟩
  have hrow :
      Finset.sum ((gridClassicalSpec w).atomInteractionNeighborhood (i, j))
        (fun b => (gridClassicalSpec w).pairwiseDobrushinCoefficient (i, j) b) =
        (1 / 2 : ℝ) * (gridClassicalSpec w).atomTotalInfluence (i, j) := by
    rw [(gridClassicalSpec w).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  have hprior_zero :
      (gridClassicalSpec w).clauseInfluenceContribution (GridClauseId.prior i j) = 0 := by
    apply (gridClassicalSpec w).clauseInfluenceContribution_eq_zero_of_card_le_one
    simp [gridClassicalSpec, gridClause, gridPriorClause_atoms]
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst hi0; subst hj0
    have hsupp00 :
        (gridClassicalSpec w).regionSupport ({(0, 0)} : Finset GridNode) =
          ({GridClauseId.prior 0 0, GridClauseId.horizontal 0 0,
            GridClauseId.vertical 0 0} : Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpec, gridRegionSupport]
    have htot :
        (gridClassicalSpec w).atomTotalInfluence (0, 0) = 2 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp00]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        gridClassicalSpec, gridClause, gridHorizontalClause_atoms, gridVerticalClause_atoms]
      ring_nf
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hi0
    have hjpred_ne : Nat.pred j ≠ j := by
      exact Nat.ne_of_lt (Nat.pred_lt hj0)
    have hsupp0j :
        (gridClassicalSpec w).regionSupport ({(0, j)} : Finset GridNode) =
          ({GridClauseId.prior 0 j, GridClauseId.horizontal 0 j,
            GridClauseId.vertical 0 j, GridClauseId.vertical 0 (Nat.pred j)} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpec, gridRegionSupport]
    have hsumv0j :
        ({GridClauseId.vertical 0 j, GridClauseId.vertical 0 (Nat.pred j)} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpec w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec, gridClause]
      · intro h
        simp at h
        exact hjpred_ne h.symm
    have htot :
        (gridClassicalSpec w).atomTotalInfluence (0, j) = 3 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp0j]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [hsumv0j]
          simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec, gridClause]
          ring_nf
        · simp
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hj0
    have hipred_ne : Nat.pred i ≠ i := by
      exact Nat.ne_of_lt (Nat.pred_lt hi0)
    have hsuppi0 :
        (gridClassicalSpec w).regionSupport ({(i, 0)} : Finset GridNode) =
          ({GridClauseId.prior i 0, GridClauseId.horizontal i 0,
            GridClauseId.horizontal (Nat.pred i) 0, GridClauseId.vertical i 0} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpec, gridRegionSupport, or_comm]
    have hsumresti0 :
        ({GridClauseId.horizontal (Nat.pred i) 0, GridClauseId.vertical i 0} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpec w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec, gridClause]
      · intro h
        cases h
    have htot :
        (gridClassicalSpec w).atomTotalInfluence (i, 0) = 3 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppi0]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [hsumresti0]
          simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec, gridClause]
          ring_nf
        · intro h
          rcases Finset.mem_insert.mp h with h | h
          · injection h with h1 h2
            exact hipred_ne h1.symm
          · simp at h
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · have hipred_ne : Nat.pred i ≠ i := by
      exact Nat.ne_of_lt (Nat.pred_lt hi0)
    have hjpred_ne : Nat.pred j ≠ j := by
      exact Nat.ne_of_lt (Nat.pred_lt hj0)
    have hsuppij :
        (gridClassicalSpec w).regionSupport ({(i, j)} : Finset GridNode) =
          ({GridClauseId.prior i j, GridClauseId.horizontal i j,
            GridClauseId.horizontal (Nat.pred i) j,
            GridClauseId.vertical i j, GridClauseId.vertical i (Nat.pred j)} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpec, gridRegionSupport, or_comm]
    have hsumvij :
        ({GridClauseId.vertical i j, GridClauseId.vertical i (Nat.pred j)} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpec w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec, gridClause]
      · intro h
        simp at h
        exact hjpred_ne h.symm
    have htot :
        (gridClassicalSpec w).atomTotalInfluence (i, j) = 4 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppij]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [hsumvij]
            simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpec,
              gridClause]
            ring_nf
          · simp
        · intro h
          rcases Finset.mem_insert.mp h with h | h
          · injection h with h1 h2
            exact hipred_ne h1.symm
          · simp at h
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]

/-- Existence for the infinite 2D grid MLN. -/
theorem exists_grid_fixedRegionCylinderDLR
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∃ μ : Measure (InfiniteWorld GridNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (gridClassicalSpec w).exists_fixedRegionCylinderDLR_of_equiv
      gridExhaustion ξ (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm

/-- End-to-end uniqueness for the infinite 2D grid. -/
theorem grid_uniqueMeasure
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridClassicalSpec w).PaperUniqueMeasure :=
  (gridClassicalSpec w).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)

/-- End-to-end WM bridge uniqueness for the infinite 2D grid. -/
theorem grid_wmBridge_unique
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (q : ConstraintQuery GridNode) :
    (infiniteMLNMassSemantics (gridClassicalSpec w) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (gridClassicalSpec w) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (gridClassicalSpec w)
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν q

/-- Quantitative local boundary-insensitivity for finite 2D-grid queries. -/
theorem grid_localQueryDiscrepancy_le_geometric
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (Δ : Region GridNode)
    (q : LocalConstraintQuery GridNode Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (gridClassicalSpec w).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := gridClassicalSpec w)
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν Δ q

end Mettapedia.Logic.MarkovLogicInfiniteGridExample
