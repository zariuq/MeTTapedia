import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Data.Finset.CastCard
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.Logic.PLNMarkovLogicInfiniteExistence

/-!
# Infinite MLN Uniqueness Frontend

This module sets up the paper-facing uniqueness layer for infinite MLNs.

The Singla--Domingos uniqueness theorem is stated for *classical* MLNs: a
ground clause together with a real log-weight.  Our current infinite-MLN
development works one layer lower, with strictly positive clause potentials.

So the first honest step toward the paper theorem is:

- add the classical infinite-MLN surface object;
- map it into the existing strictly-positive semantics;
- define the exact `total influence < 2` hypothesis from the paper;
- define the uniqueness target at the current proven DLR layer.

This does **not** yet prove the uniqueness theorem itself.  It isolates the
precise theorem object the next contraction/sensitivity proof must target.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteUniqueness

open scoped BigOperators ENNReal
open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicClauseSemantics
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive
open Mettapedia.Logic.PLNMarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.PLNMarkovLogicInfiniteExistence
open Mettapedia.Logic.PLNMarkovLogicInfiniteExistence.RegionExhaustion

/-- Classical infinite MLNs: each clause id carries a ground clause together
with a real log-weight, while local finiteness is packaged through
`regionSupport`. -/
structure ClassicalInfiniteGroundMLNSpec
    (Atom ClauseId : Type*) [DecidableEq Atom] [DecidableEq ClauseId] where
  clause : ClauseId → GroundClause Atom
  logWeight : ClauseId → ℝ
  regionSupport : Region Atom → Finset ClauseId
  regionSupport_sound :
    ∀ {Λ : Region Atom} {j : ClauseId},
      j ∈ regionSupport Λ → clauseTouchesRegion (clause j) Λ
  regionSupport_complete :
    ∀ {Λ : Region Atom} {j : ClauseId},
      clauseTouchesRegion (clause j) Λ → j ∈ regionSupport Λ

namespace ClassicalInfiniteGroundMLNSpec

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

theorem sigmoid_mul_one_sub_le_quarter (x : ℝ) :
    Real.sigmoid x * (1 - Real.sigmoid x) ≤ (1 / 4 : ℝ) := by
  have hnonneg : 0 ≤ Real.sigmoid x := Real.sigmoid_nonneg x
  have hone : Real.sigmoid x ≤ 1 := Real.sigmoid_le_one x
  nlinarith [sq_nonneg (Real.sigmoid x - (1 / 2 : ℝ))]

theorem norm_deriv_sigmoid_le_quarter (x : ℝ) :
    ‖deriv Real.sigmoid x‖ ≤ (1 / 4 : ℝ) := by
  have hsig_nonneg : 0 ≤ Real.sigmoid x := Real.sigmoid_nonneg x
  have hone_sub_nonneg : 0 ≤ 1 - Real.sigmoid x := sub_nonneg.mpr (Real.sigmoid_le_one x)
  simpa [Real.deriv_sigmoid, Real.norm_eq_abs, abs_of_nonneg hsig_nonneg,
    abs_of_nonneg hone_sub_nonneg] using
    (sigmoid_mul_one_sub_le_quarter x)

theorem abs_sigmoid_sub_le_quarter_mul_abs_sub (x y : ℝ) :
    |Real.sigmoid x - Real.sigmoid y| ≤ (1 / 4 : ℝ) * |x - y| := by
  simpa [Real.norm_eq_abs, sub_eq_add_neg, mul_comm] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le
      (f := Real.sigmoid) (s := Set.univ) (x := y) (y := x)
      (hf := fun z _ => differentiableAt_sigmoid)
      (bound := fun z _ => norm_deriv_sigmoid_le_quarter z)
      (by simp) (by simp))

/-- Forgetting the log-weight view produces the strictly positive infinite MLN
used by the existing existence/DLR development. -/
noncomputable def toStrictlyPositiveInfiniteGroundMLNSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId where
  clauseData j := classicalWeightedClause (M.clause j) (M.logWeight j)
  regionSupport := M.regionSupport
  regionSupport_sound := by
    intro Λ j hj
    exact M.regionSupport_sound hj
  regionSupport_complete := by
    intro Λ j hj
    exact M.regionSupport_complete hj
  satisfiedPotential_ne_zero := by
    intro j
    exact classicalWeightedClause_satisfiedPotential_ne_zero
      (M.clause j) (M.logWeight j)
  unsatisfiedPotential_ne_zero := by
    intro j
    exact classicalWeightedClause_unsatisfiedPotential_ne_zero
      (M.clause j) (M.logWeight j)

/-- The paper's existence theorem now transfers immediately to the classical
weighted-clause surface. -/
theorem exists_fixedRegionCylinderDLR_of_equiv
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (ξ : BoundaryCondition Atom)
    (e : ℕ ≃ Atom) :
    ∃ μ : Measure (InfiniteWorld Atom),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  exact
    Mettapedia.Logic.PLNMarkovLogicInfiniteExistence.RegionExhaustion.exists_fixedRegionCylinderDLR_of_equiv
      (E := E) (M := M.toStrictlyPositiveInfiniteGroundMLNSpec) (ξ := ξ) (e := e)

/-- A clause id lies in the singleton-region support exactly when the clause
mentions that atom. -/
theorem mem_regionSupport_singleton_iff_atom_mem_clause
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (j : ClauseId) :
    j ∈ M.regionSupport ({a} : Region Atom) ↔ a ∈ (M.clause j).atoms := by
  constructor
  · intro hj
    rcases M.regionSupport_sound hj with ⟨b, hbClause, hbRegion⟩
    have hbEq : b = a := by simpa using hbRegion
    simpa [hbEq] using hbClause
  · intro hj
    exact M.regionSupport_complete ⟨a, hj, by simp⟩

/-- Paper clause contribution:
`(|Atoms(C_j)| - 1) * |w_j|`.

Here `|Atoms(C_j)|` is the number of distinct ground atoms appearing in the
clause. We use truncated subtraction on that atom-cardinality, so unit-atom
clauses contribute zero exactly as in the paper discussion, and empty clauses do
not produce spurious negative contributions. -/
def clauseInfluenceContribution
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (j : ClauseId) : ℝ :=
  (((M.clause j).atoms.card - 1 : ℕ) : ℝ) * |M.logWeight j|

theorem clauseInfluenceContribution_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (j : ClauseId) :
    0 ≤ M.clauseInfluenceContribution j := by
  unfold clauseInfluenceContribution
  exact mul_nonneg (by positivity) (abs_nonneg _)

/-- Single-atom clauses do not contribute to the paper uniqueness coefficient. -/
theorem clauseInfluenceContribution_eq_zero_of_card_le_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (j : ClauseId)
    (hcard : (M.clause j).atoms.card ≤ 1) :
    M.clauseInfluenceContribution j = 0 := by
  unfold clauseInfluenceContribution
  have hsub : (M.clause j).atoms.card - 1 = 0 := Nat.sub_eq_zero_of_le hcard
  simp [hsub]

/-- Finite interaction neighborhood around `a`: every atom that co-occurs with
`a` in some clause touching `a`. -/
def atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (a : Atom) : Finset Atom :=
  (M.regionSupport ({a} : Region Atom)).biUnion fun j => (M.clause j).atoms.erase a

theorem mem_atomInteractionNeighborhood_iff
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) :
    b ∈ M.atomInteractionNeighborhood a ↔
      ∃ j ∈ M.regionSupport ({a} : Region Atom), b ∈ (M.clause j).atoms.erase a := by
  simp [atomInteractionNeighborhood, Finset.mem_biUnion]

theorem atoms_erase_subset_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) {j : ClauseId}
    (hj : j ∈ M.regionSupport ({a} : Region Atom)) :
    (M.clause j).atoms.erase a ⊆ M.atomInteractionNeighborhood a := by
  intro b hb
  exact (M.mem_atomInteractionNeighborhood_iff a b).2 ⟨j, hj, hb⟩

theorem self_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) :
    a ∉ M.atomInteractionNeighborhood a := by
  intro ha
  rcases (M.mem_atomInteractionNeighborhood_iff a a).1 ha with ⟨j, _, hj⟩
  simp at hj

/-- Paper-style pairwise influence from `b` into `a`: sum the absolute weights
of all clauses touching `a` that also mention `b`. -/
def pairwiseInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) : ℝ :=
  Finset.sum (M.regionSupport ({a} : Region Atom))
    (fun j => if b ∈ (M.clause j).atoms.erase a then |M.logWeight j| else 0)

theorem pairwiseInfluence_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) :
    0 ≤ M.pairwiseInfluence a b := by
  unfold pairwiseInfluence
  refine Finset.sum_nonneg ?_
  intro j hj
  split_ifs <;> positivity

theorem pairwiseInfluence_self_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) :
    M.pairwiseInfluence a a = 0 := by
  unfold pairwiseInfluence
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp

theorem pairwiseInfluence_eq_zero_of_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a) :
    M.pairwiseInfluence a b = 0 := by
  unfold pairwiseInfluence
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hnot : b ∉ (M.clause j).atoms.erase a := by
    intro hbj
    exact hb (M.atoms_erase_subset_atomInteractionNeighborhood a hj hbj)
  simp [hnot]

/-- Total paper-style influence on atom `a`: the sum over all clauses touching
`a` of `(|C_j| - 1) * |w_j|`. -/
def atomTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (a : Atom) : ℝ :=
  Finset.sum (M.regionSupport ({a} : Region Atom))
    (fun j => M.clauseInfluenceContribution j)

theorem atomTotalInfluence_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) (a : Atom) :
    0 ≤ M.atomTotalInfluence a := by
  simpa [atomTotalInfluence] using
    (Finset.sum_nonneg
      (fun j _ => M.clauseInfluenceContribution_nonneg j))

theorem atomTotalInfluence_eq_sum_pairwiseInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) :
    M.atomTotalInfluence a =
      Finset.sum (M.atomInteractionNeighborhood a) (fun b => M.pairwiseInfluence a b) := by
  classical
  unfold atomTotalInfluence pairwiseInfluence atomInteractionNeighborhood
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have ha : a ∈ (M.clause j).atoms :=
    (M.mem_regionSupport_singleton_iff_atom_mem_clause a j).1 hj
  have hfilter :
      ((M.regionSupport ({a} : Region Atom)).biUnion
          fun j => (M.clause j).atoms.erase a).filter
          (fun b => b ∈ (M.clause j).atoms.erase a) =
        (M.clause j).atoms.erase a := by
    ext b
    constructor
    · intro hb
      exact (Finset.mem_filter.mp hb).2
    · intro hb
      exact Finset.mem_filter.mpr
        ⟨M.atoms_erase_subset_atomInteractionNeighborhood a hj hb, hb⟩
  calc
    M.clauseInfluenceContribution j
      = ((((M.clause j).atoms.card - 1 : ℕ) : ℝ) * |M.logWeight j|) := by
          rfl
    _ = (((M.clause j).atoms.erase a).card : ℝ) * |M.logWeight j| := by
          rw [Finset.card_erase_of_mem ha]
    _ = Finset.sum ((M.clause j).atoms.erase a) (fun _ => |M.logWeight j|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = Finset.sum
        ((((M.regionSupport ({a} : Region Atom)).biUnion
          fun j => (M.clause j).atoms.erase a).filter
            (fun b => b ∈ (M.clause j).atoms.erase a)))
        (fun _ => |M.logWeight j|) := by
          rw [hfilter]
    _ = Finset.sum
        ((M.regionSupport ({a} : Region Atom)).biUnion
          (fun j => (M.clause j).atoms.erase a))
        (fun b =>
          if b ∈ (M.clause j).atoms.erase a then |M.logWeight j| else 0) := by
          rw [← Finset.sum_filter]

/-- The paper's small-total-influence hypothesis:
the total interaction weight on every atom is strictly less than `2`. -/
def PaperSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) : Prop :=
  ∀ a : Atom, M.atomTotalInfluence a < 2

theorem paperSmallTotalInfluence_iff_pairwiseRowSums_lt_two
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    M.PaperSmallTotalInfluence ↔
      ∀ a : Atom,
        Finset.sum (M.atomInteractionNeighborhood a) (fun b => M.pairwiseInfluence a b) < 2 := by
  constructor
  · intro h a
    simpa [PaperSmallTotalInfluence, M.atomTotalInfluence_eq_sum_pairwiseInfluence a] using h a
  · intro h a
    simpa [PaperSmallTotalInfluence, M.atomTotalInfluence_eq_sum_pairwiseInfluence a] using h a

/-- Two boundary conditions agree off the distinguished atom `b`. -/
def AgreesOffAtom
    (b : Atom) (ξ₁ ξ₂ : BoundaryCondition Atom) : Prop :=
  ∀ ⦃c : Atom⦄, c ≠ b → ξ₁ c = ξ₂ c

/-- The canonical singleton local assignment setting atom `a` to `v`. -/
def singletonAssignment
    (a : Atom) (v : Bool) : LocalAssignment Atom ({a} : Region Atom) :=
  fun _ => v

omit [DecidableEq Atom] in
@[simp] theorem singletonAssignment_apply
    (a : Atom) (v : Bool) (i : RegionAtom Atom ({a} : Region Atom)) :
    singletonAssignment (Atom := Atom) a v i = v := by
  rfl

/-- A one-site local assignment is exactly the same data as a Boolean value. -/
noncomputable def singletonAssignmentEquiv
    (a : Atom) : LocalAssignment Atom ({a} : Region Atom) ≃ Bool where
  toFun x := x ⟨a, by simp⟩
  invFun v := singletonAssignment (Atom := Atom) a v
  left_inv x := by
    funext i
    have hi : i = ⟨a, by simp⟩ := by
      apply Subtype.ext
      exact Finset.mem_singleton.mp i.2
    simp [singletonAssignment, hi]
  right_inv v := by
    rfl

/-- The singleton local assignments where atom `a` is true. On a Boolean site,
this event determines the full one-site marginal. -/
def singletonTrueAssignmentSet
    (a : Atom) : Set (LocalAssignment Atom ({a} : Region Atom)) :=
  {x | x ⟨a, by simp⟩ = true}

omit [DecidableEq Atom] in
theorem measurableSet_singletonTrueAssignmentSet
    (a : Atom) :
    MeasurableSet (singletonTrueAssignmentSet (Atom := Atom) a) := by
  unfold singletonTrueAssignmentSet
  exact (Set.to_countable {x : LocalAssignment Atom ({a} : Region Atom) | x ⟨a, by simp⟩ = true}).measurableSet

/-- The one-site kernel probability that atom `a` is true under boundary
condition `ξ`, viewed on the classical weighted-clause surface. -/
noncomputable def singletonKernelTrueProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) : ℝ :=
  ENNReal.toReal
    (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ
      (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a)))

/-- Real-valued sensitivity of the one-site true-marginal under two boundary
conditions. -/
noncomputable def singletonKernelTrueSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) : ℝ :=
  |M.singletonKernelTrueProb a ξ₁ - M.singletonKernelTrueProb a ξ₂|

theorem singletonKernelTrueSensitivity_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) :
    0 ≤ M.singletonKernelTrueSensitivity a ξ₁ ξ₂ := by
  unfold singletonKernelTrueSensitivity
  exact abs_nonneg _

omit [DecidableEq Atom] in
@[simp] theorem mem_singletonTrueAssignmentSet_singletonAssignment
    (a : Atom) (v : Bool) :
    singletonAssignment (Atom := Atom) a v ∈ singletonTrueAssignmentSet a ↔ v = true := by
  simp [singletonTrueAssignmentSet, singletonAssignment]

theorem finiteVolumePartition_singleton_eq_true_add_false
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition
        ({a} : Region Atom) ξ =
      M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
          ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ +
        M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
          ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ := by
  classical
  let Minf := M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  unfold InfiniteGroundMLNSpec.finiteVolumePartition
  calc
    ∑ x : LocalAssignment Atom ({a} : Region Atom),
        Minf.finiteVolumeWeight ({a} : Region Atom) x ξ
      =
        ∑ b : Bool,
          Minf.finiteVolumeWeight ({a} : Region Atom)
            (singletonAssignment (Atom := Atom) a b) ξ := by
          simpa [Minf] using
            (Fintype.sum_equiv
              (singletonAssignmentEquiv (Atom := Atom) a)
              (fun x : LocalAssignment Atom ({a} : Region Atom) =>
                Minf.finiteVolumeWeight ({a} : Region Atom) x ξ)
              (fun b : Bool =>
                Minf.finiteVolumeWeight ({a} : Region Atom)
                  (singletonAssignment (Atom := Atom) a b) ξ)
              (fun x => by
                exact (congrArg
                  (fun y =>
                    Minf.finiteVolumeWeight ({a} : Region Atom) y ξ)
                  ((singletonAssignmentEquiv (Atom := Atom) a).left_inv x)).symm))
    _ =
        Minf.finiteVolumeWeight ({a} : Region Atom)
            (singletonAssignment (Atom := Atom) a true) ξ +
          Minf.finiteVolumeWeight ({a} : Region Atom)
            (singletonAssignment (Atom := Atom) a false) ξ := by
          rw [Fintype.sum_bool]

theorem finiteVolumeCylinderMass_singletonTrue_eq_trueWeight
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    finiteVolumeCylinderMass
        M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({a} : Region Atom) ξ ({a} : Region Atom) (singletonTrueAssignmentSet a) =
      M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
        ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ := by
  classical
  let Minf := M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  unfold finiteVolumeCylinderMass
  calc
    ∑ x : LocalAssignment Atom ({a} : Region Atom),
        (if patch ({a} : Region Atom) x ξ ∈
            MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
          Minf.finiteVolumeWeight ({a} : Region Atom) x ξ
        else 0)
      =
        ∑ b : Bool,
          (if patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a b) ξ ∈
              MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
            Minf.finiteVolumeWeight ({a} : Region Atom)
              (singletonAssignment (Atom := Atom) a b) ξ
          else 0) := by
          simpa [Minf] using
            (Fintype.sum_equiv
              (singletonAssignmentEquiv (Atom := Atom) a)
              (fun x : LocalAssignment Atom ({a} : Region Atom) =>
                if patch ({a} : Region Atom) x ξ ∈
                    MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
                  Minf.finiteVolumeWeight ({a} : Region Atom) x ξ
                else 0)
              (fun b : Bool =>
                if patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a b) ξ ∈
                    MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
                  Minf.finiteVolumeWeight ({a} : Region Atom)
                    (singletonAssignment (Atom := Atom) a b) ξ
                else 0)
              (fun x => by
                exact (congrArg
                  (fun y =>
                    if patch ({a} : Region Atom) y ξ ∈
                        MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
                      Minf.finiteVolumeWeight ({a} : Region Atom) y ξ
                    else 0)
                  ((singletonAssignmentEquiv (Atom := Atom) a).left_inv x)).symm))
    _ =
        (if patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ ∈
              MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
            Minf.finiteVolumeWeight ({a} : Region Atom)
              (singletonAssignment (Atom := Atom) a true) ξ
          else 0) +
        (if patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ ∈
              MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a) then
            Minf.finiteVolumeWeight ({a} : Region Atom)
              (singletonAssignment (Atom := Atom) a false) ξ
          else 0) := by
          rw [Fintype.sum_bool]
    _ =
        Minf.finiteVolumeWeight ({a} : Region Atom)
          (singletonAssignment (Atom := Atom) a true) ξ +
        0 := by
          simp [MeasureTheory.mem_cylinder, singletonAssignment, singletonTrueAssignmentSet, patch]
    _ =
        Minf.finiteVolumeWeight ({a} : Region Atom)
          (singletonAssignment (Atom := Atom) a true) ξ := by
          simp

theorem singletonKernelTrueProb_eq_trueWeight_mul_invPartition
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonKernelTrueProb a ξ =
      ENNReal.toReal
        (M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
            ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ *
          (M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition
            ({a} : Region Atom) ξ)⁻¹) := by
  let Minf := M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  have hZ : Minf.finiteVolumePartition ({a} : Region Atom) ξ ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ
  unfold singletonKernelTrueProb StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
  rw [finiteVolumeWorldMeasure_cylinder
      (M := Minf)
      (Λ := ({a} : Region Atom))
      (I := ({a} : Region Atom))
      (S := singletonTrueAssignmentSet a)
      (hS := measurableSet_singletonTrueAssignmentSet a)
      (ξ := ξ)
      hZ]
  rw [M.finiteVolumeCylinderMass_singletonTrue_eq_trueWeight]

theorem singletonKernelTrueProb_eq_trueWeight_mul_inv_true_add_false
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonKernelTrueProb a ξ =
      ENNReal.toReal
        (M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
            ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ *
          (M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
              ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ +
            M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
              ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ)⁻¹) := by
  rw [M.singletonKernelTrueProb_eq_trueWeight_mul_invPartition a ξ]
  congr 1
  rw [M.finiteVolumePartition_singleton_eq_true_add_false a ξ]

/-- The singleton assignment exponent is the sum of the log-weights of the
clauses touching `a` that are satisfied under that one-site assignment. -/
noncomputable def singletonAssignmentExponent
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (v : Bool) (ξ : BoundaryCondition Atom) : ℝ :=
  Finset.sum (M.regionSupport ({a} : Region Atom)) fun j =>
    if (M.clause j).holds (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a v) ξ) then
      M.logWeight j
    else 0

omit [DecidableEq Atom] in
theorem classicalWeightedClause_eval_eq_ofReal_indicator_exp
    (C : GroundClause Atom) (w : ℝ) (W : InfiniteWorld Atom) :
    (classicalWeightedClause C w).eval W =
      ENNReal.ofReal (if C.holds W then Real.exp w else 1) := by
  classical
  unfold WeightedGroundClause.eval classicalWeightedClause
  by_cases h : C.holds W <;> simp [h]

theorem finiteVolumeWeight_singletonAssignment_eq_exp_exponent
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (v : Bool) (ξ : BoundaryCondition Atom) :
    M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
        ({a} : Region Atom) (singletonAssignment (Atom := Atom) a v) ξ =
      ENNReal.ofReal (Real.exp (M.singletonAssignmentExponent a v ξ)) := by
  classical
  let W : InfiniteWorld Atom :=
    patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a v) ξ
  calc
    M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWeight
        ({a} : Region Atom) (singletonAssignment (Atom := Atom) a v) ξ
      =
        Finset.prod (M.regionSupport ({a} : Region Atom)) fun j =>
          ENNReal.ofReal (if (M.clause j).holds W then Real.exp (M.logWeight j) else 1) := by
            unfold StrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
              InfiniteGroundMLNSpec.finiteVolumeWeight
            refine Finset.prod_congr rfl ?_
            intro j hj
            simpa [W] using
              classicalWeightedClause_eval_eq_ofReal_indicator_exp
                (C := M.clause j) (w := M.logWeight j) (W := W)
    _ =
        ENNReal.ofReal
          (Finset.prod (M.regionSupport ({a} : Region Atom)) fun j =>
            if (M.clause j).holds W then Real.exp (M.logWeight j) else 1) := by
            symm
            refine ENNReal.ofReal_prod_of_nonneg ?_
            intro j hj
            split_ifs <;> positivity
    _ =
        ENNReal.ofReal
          (Finset.prod (M.regionSupport ({a} : Region Atom)) fun j =>
            Real.exp (if (M.clause j).holds W then M.logWeight j else 0)) := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro j hj
            split_ifs <;> simp
    _ =
        ENNReal.ofReal
          (Real.exp
            (Finset.sum (M.regionSupport ({a} : Region Atom)) fun j =>
              if (M.clause j).holds W then M.logWeight j else 0)) := by
            congr 1
            rw [← Real.exp_sum]
    _ =
        ENNReal.ofReal (Real.exp (M.singletonAssignmentExponent a v ξ)) := by
            simp [singletonAssignmentExponent, W]

theorem finiteVolumePartition_singleton_eq_exp_true_add_exp_false
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition
        ({a} : Region Atom) ξ =
      ENNReal.ofReal (Real.exp (M.singletonAssignmentExponent a true ξ) +
        Real.exp (M.singletonAssignmentExponent a false ξ)) := by
  rw [M.finiteVolumePartition_singleton_eq_true_add_false a ξ]
  rw [M.finiteVolumeWeight_singletonAssignment_eq_exp_exponent a true ξ]
  rw [M.finiteVolumeWeight_singletonAssignment_eq_exp_exponent a false ξ]
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]

theorem singletonKernelTrueProb_eq_exp_div_exp_add_exp
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonKernelTrueProb a ξ =
      Real.exp (M.singletonAssignmentExponent a true ξ) /
        (Real.exp (M.singletonAssignmentExponent a true ξ) +
          Real.exp (M.singletonAssignmentExponent a false ξ)) := by
  rw [M.singletonKernelTrueProb_eq_trueWeight_mul_inv_true_add_false a ξ]
  rw [M.finiteVolumeWeight_singletonAssignment_eq_exp_exponent a true ξ]
  rw [M.finiteVolumeWeight_singletonAssignment_eq_exp_exponent a false ξ]
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  have hsum_pos :
      0 <
        Real.exp (M.singletonAssignmentExponent a true ξ) +
          Real.exp (M.singletonAssignmentExponent a false ξ) := by
    positivity
  rw [show
      (ENNReal.ofReal
        (Real.exp (M.singletonAssignmentExponent a true ξ) +
          Real.exp (M.singletonAssignmentExponent a false ξ)))⁻¹ =
        ENNReal.ofReal
          ((Real.exp (M.singletonAssignmentExponent a true ξ) +
            Real.exp (M.singletonAssignmentExponent a false ξ))⁻¹) by
      exact (ENNReal.ofReal_inv_of_pos hsum_pos).symm]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 hsum_pos.le)]
  rw [div_eq_mul_inv]

/-- One-site log-odds parameter suggested by the explicit Bernoulli formulas. -/
noncomputable def singletonLogOdds
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) : ℝ :=
  M.singletonAssignmentExponent a true ξ -
    M.singletonAssignmentExponent a false ξ

theorem singletonKernelTrueProb_eq_inv_one_add_exp_neg_singletonLogOdds
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonKernelTrueProb a ξ =
      1 / (1 + Real.exp (-M.singletonLogOdds a ξ)) := by
  rw [M.singletonKernelTrueProb_eq_exp_div_exp_add_exp a ξ]
  let x := M.singletonAssignmentExponent a true ξ
  let y := M.singletonAssignmentExponent a false ξ
  have hx : Real.exp x ≠ 0 := by
    positivity
  calc
    Real.exp x / (Real.exp x + Real.exp y)
      = 1 / (1 + Real.exp y / Real.exp x) := by
          field_simp [hx]
    _ = 1 / (1 + Real.exp (y - x)) := by
          rw [Real.exp_sub]
    _ = 1 / (1 + Real.exp (-(x - y))) := by
          congr 2
          ring_nf
    _ = 1 / (1 + Real.exp (-M.singletonLogOdds a ξ)) := by
          simp [singletonLogOdds, x, y]

theorem singletonKernelTrueProb_eq_sigmoid_singletonLogOdds
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonKernelTrueProb a ξ = Real.sigmoid (M.singletonLogOdds a ξ) := by
  simpa [Real.sigmoid_def, one_div] using
    M.singletonKernelTrueProb_eq_inv_one_add_exp_neg_singletonLogOdds a ξ

namespace GroundClause

variable {Atom : Type*} [DecidableEq Atom]

/-- A clause already satisfied by some literal whose atom is outside the
distinguished singleton site `a`. -/
def boundarySatisfiedExcluding
    (C : GroundClause Atom) (a : Atom) (ξ : BoundaryCondition Atom) : Prop :=
  ∃ l, l ∈ C ∧ l.atom ≠ a ∧ Literal.holds ξ l

noncomputable instance boundarySatisfiedExcludingDecidable
    (C : GroundClause Atom) (a : Atom) (ξ : BoundaryCondition Atom) :
    Decidable (GroundClause.boundarySatisfiedExcluding C a ξ) := by
  classical
  unfold GroundClause.boundarySatisfiedExcluding
  infer_instance

theorem boundarySatisfiedExcluding_congr_of_agreesOffAtom_of_not_mem_atoms_erase
    (C : GroundClause Atom)
    (a b : Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂)
    (hb : b ∉ C.atoms.erase a) :
    GroundClause.boundarySatisfiedExcluding C a ξ₁ ↔
      GroundClause.boundarySatisfiedExcluding C a ξ₂ := by
  constructor
  · rintro ⟨l, hl, hla, hh⟩
    refine ⟨l, hl, hla, ?_⟩
    have hlAtoms : l.atom ∈ C.atoms := C.atom_mem_atoms hl
    have hlb : l.atom ≠ b := by
      intro hlbEq
      exact hb <| Finset.mem_erase.mpr ⟨hlbEq ▸ hla, hlbEq ▸ hlAtoms⟩
    cases l with
    | pos c =>
        simp [Literal.holds] at hh ⊢
        calc
          ξ₂ c = ξ₁ c := (hag hlb).symm
          _ = true := hh
    | neg c =>
        simp [Literal.holds] at hh ⊢
        calc
          ξ₂ c = ξ₁ c := (hag hlb).symm
          _ = false := hh
  · rintro ⟨l, hl, hla, hh⟩
    refine ⟨l, hl, hla, ?_⟩
    have hlAtoms : l.atom ∈ C.atoms := C.atom_mem_atoms hl
    have hlb : l.atom ≠ b := by
      intro hlbEq
      exact hb <| Finset.mem_erase.mpr ⟨hlbEq ▸ hla, hlbEq ▸ hlAtoms⟩
    cases l with
    | pos c =>
        simp [Literal.holds] at hh ⊢
        calc
          ξ₁ c = ξ₂ c := hag hlb
          _ = true := hh
    | neg c =>
        simp [Literal.holds] at hh ⊢
        calc
          ξ₁ c = ξ₂ c := hag hlb
          _ = false := hh

theorem holds_patch_singletonAssignment_iff
    (C : GroundClause Atom)
    (a : Atom) (v : Bool) (ξ : BoundaryCondition Atom) :
    C.holds (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a v) ξ) ↔
      GroundClause.boundarySatisfiedExcluding C a ξ ∨
        (Literal.pos a ∈ C ∧ v = true) ∨
        (Literal.neg a ∈ C ∧ v = false) := by
  constructor
  · rintro ⟨l, hl, hh⟩
    by_cases hla : l.atom = a
    · cases l with
      | pos c =>
          have hc : c = a := hla
          right
          left
          refine ⟨?_, ?_⟩
          · simpa [hc] using hl
          · simp [Literal.holds, patch, singletonAssignment, hc] at hh
            exact hh
      | neg c =>
          have hc : c = a := hla
          right
          right
          refine ⟨?_, ?_⟩
          · simpa [hc] using hl
          · simp [Literal.holds, patch, singletonAssignment, hc] at hh
            exact hh
    · left
      refine ⟨l, hl, hla, ?_⟩
      cases l with
      | pos c =>
          have hnot : c ∉ ({a} : Region Atom) := by simpa using hla
          simpa [Literal.holds, patch, singletonAssignment, hnot] using hh
      | neg c =>
          have hnot : c ∉ ({a} : Region Atom) := by simpa using hla
          simpa [Literal.holds, patch, singletonAssignment, hnot] using hh
  · rintro (hother | hpos | hneg)
    · rcases hother with ⟨l, hl, hla, hh⟩
      refine ⟨l, hl, ?_⟩
      cases l with
      | pos c =>
          have hnot : c ∉ ({a} : Region Atom) := by simpa using hla
          simpa [Literal.holds, patch, singletonAssignment, hnot] using hh
      | neg c =>
          have hnot : c ∉ ({a} : Region Atom) := by simpa using hla
          simpa [Literal.holds, patch, singletonAssignment, hnot] using hh
    · rcases hpos with ⟨hl, hv⟩
      refine ⟨Literal.pos a, hl, ?_⟩
      simp [Literal.holds, patch, singletonAssignment, hv]
    · rcases hneg with ⟨hl, hv⟩
      refine ⟨Literal.neg a, hl, ?_⟩
      simp [Literal.holds, patch, singletonAssignment, hv]

end GroundClause

/-- The contribution of a single clause to the one-site log-odds at atom `a`. -/
noncomputable def singletonLogOddsClauseContribution
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (j : ClauseId) (ξ : BoundaryCondition Atom) : ℝ :=
  (if (M.clause j).holds
      (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ)
    then M.logWeight j else 0) -
  (if (M.clause j).holds
      (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ)
    then M.logWeight j else 0)

/-- The sign-determined clause bias when no outside literal is already
satisfied. -/
noncomputable def singletonLogOddsClauseBase
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (j : ClauseId) : ℝ :=
  (if Literal.pos a ∈ M.clause j then M.logWeight j else 0) -
  (if Literal.neg a ∈ M.clause j then M.logWeight j else 0)

theorem singletonLogOdds_eq_sum_clauseContribution
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (ξ : BoundaryCondition Atom) :
    M.singletonLogOdds a ξ =
      Finset.sum (M.regionSupport ({a} : Region Atom))
        (fun j => M.singletonLogOddsClauseContribution a j ξ) := by
  unfold singletonLogOdds singletonAssignmentExponent singletonLogOddsClauseContribution
  rw [Finset.sum_sub_distrib]

theorem singletonLogOddsClauseContribution_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (j : ClauseId) (ξ : BoundaryCondition Atom) :
    M.singletonLogOddsClauseContribution a j ξ =
      if GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ then
        0
      else
        M.singletonLogOddsClauseBase a j := by
  have htrue :
      (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ) ↔
        GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ ∨ Literal.pos a ∈ M.clause j := by
    simpa using
      (GroundClause.holds_patch_singletonAssignment_iff
        (C := M.clause j) (a := a) (v := true) (ξ := ξ))
  have hfalse :
      (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ) ↔
        GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ ∨ Literal.neg a ∈ M.clause j := by
    simpa using
      (GroundClause.holds_patch_singletonAssignment_iff
        (C := M.clause j) (a := a) (v := false) (ξ := ξ))
  by_cases hother : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ
  · have hholds_true :
        (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ) := by
      exact htrue.mpr (Or.inl hother)
    have hholds_false :
        (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ) := by
      exact hfalse.mpr (Or.inl hother)
    simp [singletonLogOddsClauseContribution, hother, hholds_true, hholds_false]
  · have hholds_true :
        (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a true) ξ) ↔
        Literal.pos a ∈ M.clause j := by
      constructor
      · intro hh
        rcases htrue.mp hh with h | h
        · exact False.elim (hother h)
        · exact h
      · intro hh
        exact htrue.mpr (Or.inr hh)
    have hholds_false :
        (M.clause j).holds
          (patch ({a} : Region Atom) (singletonAssignment (Atom := Atom) a false) ξ) ↔
        Literal.neg a ∈ M.clause j := by
      constructor
      · intro hh
        rcases hfalse.mp hh with h | h
        · exact False.elim (hother h)
        · exact h
      · intro hh
        exact hfalse.mpr (Or.inr hh)
    simp [singletonLogOddsClauseContribution, singletonLogOddsClauseBase, hother,
      hholds_true, hholds_false]

theorem singletonLogOddsClauseBase_abs_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) (j : ClauseId) :
    |M.singletonLogOddsClauseBase a j| ≤ |M.logWeight j| := by
  by_cases hpos : Literal.pos a ∈ M.clause j
  · by_cases hneg : Literal.neg a ∈ M.clause j
    · simp [singletonLogOddsClauseBase, hpos, hneg]
    · simp [singletonLogOddsClauseBase, hpos, hneg]
  · by_cases hneg : Literal.neg a ∈ M.clause j
    · simp [singletonLogOddsClauseBase, hpos, hneg]
    · simp [singletonLogOddsClauseBase, hpos, hneg]

theorem singletonLogOddsClauseContribution_abs_sub_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) (j : ClauseId)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    |M.singletonLogOddsClauseContribution a j ξ₁ -
        M.singletonLogOddsClauseContribution a j ξ₂| ≤
      if b ∈ (M.clause j).atoms.erase a then |M.logWeight j| else 0 := by
  by_cases hb : b ∈ (M.clause j).atoms.erase a
  · have hform1 := M.singletonLogOddsClauseContribution_eq a j ξ₁
    have hform2 := M.singletonLogOddsClauseContribution_eq a j ξ₂
    rw [hform1, hform2, if_pos hb]
    by_cases hother1 : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₁
    · by_cases hother2 : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₂
      · simp [hother1, hother2]
      · have hbase := M.singletonLogOddsClauseBase_abs_le a j
        simpa [hother1, hother2, abs_sub_comm] using hbase
    · by_cases hother2 : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₂
      · have hbase := M.singletonLogOddsClauseBase_abs_le a j
        simpa [hother1, hother2] using hbase
      · simp [hother1, hother2]
  · have hother :
      GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₁ ↔
        GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₂ :=
      GroundClause.boundarySatisfiedExcluding_congr_of_agreesOffAtom_of_not_mem_atoms_erase
        (C := M.clause j) (a := a) (b := b) hag hb
    have hcontrib :
        M.singletonLogOddsClauseContribution a j ξ₁ =
          M.singletonLogOddsClauseContribution a j ξ₂ := by
      rw [M.singletonLogOddsClauseContribution_eq a j ξ₁,
        M.singletonLogOddsClauseContribution_eq a j ξ₂]
      by_cases h1 : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₁
      · have h2 : GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₂ := hother.mp h1
        simp [h1, h2]
      · have h2 : ¬ GroundClause.boundarySatisfiedExcluding (M.clause j) a ξ₂ := by
          intro h2
          exact h1 (hother.mpr h2)
        simp [h1, h2]
    rw [if_neg hb, hcontrib, sub_self, abs_zero]

theorem singletonLogOdds_abs_sub_le_pairwiseInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    |M.singletonLogOdds a ξ₁ - M.singletonLogOdds a ξ₂| ≤
      M.pairwiseInfluence a b := by
  let s := M.regionSupport ({a} : Region Atom)
  rw [M.singletonLogOdds_eq_sum_clauseContribution a ξ₁,
    M.singletonLogOdds_eq_sum_clauseContribution a ξ₂]
  rw [← Finset.sum_sub_distrib]
  have hsumAbs :
      abs (s.sum fun j =>
        M.singletonLogOddsClauseContribution a j ξ₁ -
          M.singletonLogOddsClauseContribution a j ξ₂) ≤
        s.sum fun j =>
          |M.singletonLogOddsClauseContribution a j ξ₁ -
            M.singletonLogOddsClauseContribution a j ξ₂| := by
    simpa [s] using
      (Finset.abs_sum_le_sum_abs
        (s := s)
        (f := fun j =>
          M.singletonLogOddsClauseContribution a j ξ₁ -
            M.singletonLogOddsClauseContribution a j ξ₂))
  calc
    abs (s.sum fun j =>
        M.singletonLogOddsClauseContribution a j ξ₁ -
          M.singletonLogOddsClauseContribution a j ξ₂) ≤
      s.sum fun j =>
        |M.singletonLogOddsClauseContribution a j ξ₁ -
          M.singletonLogOddsClauseContribution a j ξ₂| := hsumAbs
    _ ≤ s.sum fun j =>
        if b ∈ (M.clause j).atoms.erase a then |M.logWeight j| else 0 := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact M.singletonLogOddsClauseContribution_abs_sub_le a b j hag
    _ = M.pairwiseInfluence a b := by
          simp [pairwiseInfluence, s]

theorem boundaryClauseSupportRegion_singleton_eq_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) :
    boundaryClauseSupportRegion
        M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec ({a} : Region Atom) =
      M.atomInteractionNeighborhood a := by
  classical
  ext b
  constructor
  · intro hb
    simp [boundaryClauseSupportRegion] at hb
    rcases hb with ⟨j, hj, hbClause, hbNot⟩
    exact (M.mem_atomInteractionNeighborhood_iff a b).2
      ⟨j, hj, Finset.mem_erase.mpr ⟨hbNot, hbClause⟩⟩
  · intro hb
    rcases (M.mem_atomInteractionNeighborhood_iff a b).1 hb with ⟨j, hj, hbj⟩
    have hbClause : b ∈ (M.clause j).atoms := (Finset.mem_erase.mp hbj).2
    have hbNot : b ∉ ({a} : Region Atom) := by
      simpa using (Finset.mem_erase.mp hbj).1
    change b ∈
      (M.regionSupport ({a} : Region Atom)).biUnion
        (fun j => (M.clause j).atoms \ ({a} : Region Atom))
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_sdiff.mpr ⟨hbClause, hbNot⟩⟩

theorem cylinderBoundarySupportRegion_singleton_eq_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom) :
    cylinderBoundarySupportRegion
        M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({a} : Region Atom) ({a} : Region Atom) =
      M.atomInteractionNeighborhood a := by
  classical
  rw [cylinderBoundarySupportRegion, M.boundaryClauseSupportRegion_singleton_eq_atomInteractionNeighborhood]
  have hout :
      outsideRegion ({a} : Region Atom) ({a} : Region Atom) = (∅ : Region Atom) := by
    ext b
    simp [outsideRegion]
  simp [hout]

theorem singletonKernel_cylinder_eq_of_restrict_atomInteractionNeighborhood_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (S : Set (LocalAssignment Atom ({a} : Region Atom)))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hrestrict :
      Finset.restrict (M.atomInteractionNeighborhood a) ξ₁ =
        Finset.restrict (M.atomInteractionNeighborhood a) ξ₂) :
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₁
        (MeasureTheory.cylinder ({a} : Region Atom) S) =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₂
        (MeasureTheory.cylinder ({a} : Region Atom) S) := by
  have hrestrict' :
      Finset.restrict
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom)) ξ₁ =
        Finset.restrict
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom)) ξ₂ := by
    rw [M.cylinderBoundarySupportRegion_singleton_eq_atomInteractionNeighborhood a]
    exact hrestrict
  exact
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq'
      (M := M.toStrictlyPositiveInfiniteGroundMLNSpec)
      (Λ := ({a} : Region Atom))
      (I := ({a} : Region Atom))
      (S := S)
      hS
      (ξ₁ := ξ₁)
      (ξ₂ := ξ₂)
      hrestrict'

theorem singletonKernel_cylinder_eq_of_agreesOffAtom_of_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a)
    (S : Set (LocalAssignment Atom ({a} : Region Atom)))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₁
        (MeasureTheory.cylinder ({a} : Region Atom) S) =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₂
        (MeasureTheory.cylinder ({a} : Region Atom) S) := by
  apply M.singletonKernel_cylinder_eq_of_restrict_atomInteractionNeighborhood_eq a S hS
  funext c
  simp [Finset.restrict]
  exact hag (by
    intro hcb
    exact hb (hcb ▸ c.2))

theorem singletonKernel_cylinder_eq_of_pairwiseInfluence_zero_outsideNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a)
    (S : Set (LocalAssignment Atom ({a} : Region Atom)))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.pairwiseInfluence a b = 0 ∧
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₁
          (MeasureTheory.cylinder ({a} : Region Atom) S) =
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₂
          (MeasureTheory.cylinder ({a} : Region Atom) S) := by
  refine ⟨M.pairwiseInfluence_eq_zero_of_not_mem_atomInteractionNeighborhood a b hb, ?_⟩
  exact M.singletonKernel_cylinder_eq_of_agreesOffAtom_of_not_mem_atomInteractionNeighborhood
    a b hb S hS hag

theorem singletonKernelTrueSensitivity_eq_zero_of_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.singletonKernelTrueSensitivity a ξ₁ ξ₂ = 0 := by
  have hmeasure :
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₁
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a)) =
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          M.toStrictlyPositiveInfiniteGroundMLNSpec ({a} : Region Atom) ξ₂
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a)) :=
    M.singletonKernel_cylinder_eq_of_agreesOffAtom_of_not_mem_atomInteractionNeighborhood
      a b hb (singletonTrueAssignmentSet a) (measurableSet_singletonTrueAssignmentSet a) hag
  have hprob :
      M.singletonKernelTrueProb a ξ₁ = M.singletonKernelTrueProb a ξ₂ := by
    unfold singletonKernelTrueProb
    exact congrArg ENNReal.toReal hmeasure
  unfold singletonKernelTrueSensitivity
  rw [hprob, sub_self, abs_zero]

theorem singletonKernelTrueSensitivity_le_pairwiseInfluence_of_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.singletonKernelTrueSensitivity a ξ₁ ξ₂ ≤ M.pairwiseInfluence a b := by
  rw [M.singletonKernelTrueSensitivity_eq_zero_of_not_mem_atomInteractionNeighborhood a b hb hag]
  rw [M.pairwiseInfluence_eq_zero_of_not_mem_atomInteractionNeighborhood a b hb]

theorem singletonKernelTrueSensitivity_le_quarter_mul_pairwiseInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.singletonKernelTrueSensitivity a ξ₁ ξ₂ ≤
      (1 / 4 : ℝ) * M.pairwiseInfluence a b := by
  unfold singletonKernelTrueSensitivity
  rw [M.singletonKernelTrueProb_eq_sigmoid_singletonLogOdds a ξ₁,
    M.singletonKernelTrueProb_eq_sigmoid_singletonLogOdds a ξ₂]
  have hsig :=
    abs_sigmoid_sub_le_quarter_mul_abs_sub
      (M.singletonLogOdds a ξ₁) (M.singletonLogOdds a ξ₂)
  have hlog := M.singletonLogOdds_abs_sub_le_pairwiseInfluence a b hag
  exact le_trans hsig <| mul_le_mul_of_nonneg_left hlog (by positivity)

/-- The full `L1` discrepancy of the one-site Boolean kernel, written in terms
of the `true` and `false` singleton masses. For a Boolean site, this is the
exact two-state coefficient that feeds the Dobrushin contraction matrix. -/
noncomputable def singletonKernelBernoulliL1Sensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) : ℝ :=
  |M.singletonKernelTrueProb a ξ₁ - M.singletonKernelTrueProb a ξ₂| +
    |(1 - M.singletonKernelTrueProb a ξ₁) -
      (1 - M.singletonKernelTrueProb a ξ₂)|

theorem singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) :
    M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ =
      2 * M.singletonKernelTrueSensitivity a ξ₁ ξ₂ := by
  unfold singletonKernelBernoulliL1Sensitivity singletonKernelTrueSensitivity
  let p₁ := M.singletonKernelTrueProb a ξ₁
  let p₂ := M.singletonKernelTrueProb a ξ₂
  have hfalse : |(1 - p₁) - (1 - p₂)| = |p₁ - p₂| := by
    have hneg : (1 - p₁) - (1 - p₂) = -(p₁ - p₂) := by ring
    rw [hneg, abs_neg]
  rw [hfalse]
  ring

theorem singletonKernelBernoulliL1Sensitivity_le_half_mul_pairwiseInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ ≤
      (1 / 2 : ℝ) * M.pairwiseInfluence a b := by
  rw [M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity a ξ₁ ξ₂]
  have hsens := M.singletonKernelTrueSensitivity_le_quarter_mul_pairwiseInfluence a b hag
  calc
    2 * M.singletonKernelTrueSensitivity a ξ₁ ξ₂ ≤
        2 * ((1 / 4 : ℝ) * M.pairwiseInfluence a b) := by
          exact mul_le_mul_of_nonneg_left hsens (by positivity)
    _ = (1 / 2 : ℝ) * M.pairwiseInfluence a b := by ring

/-- The pairwise Dobrushin coefficient suggested by the new one-site Boolean
kernel bound. -/
noncomputable def pairwiseDobrushinCoefficient
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) : ℝ :=
  (1 / 2 : ℝ) * M.pairwiseInfluence a b

theorem singletonKernelBernoulliL1Sensitivity_le_pairwiseDobrushinCoefficient
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOffAtom b ξ₁ ξ₂) :
    M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ ≤
      M.pairwiseDobrushinCoefficient a b := by
  simpa [pairwiseDobrushinCoefficient] using
    M.singletonKernelBernoulliL1Sensitivity_le_half_mul_pairwiseInfluence a b hag

theorem pairwiseDobrushinCoefficient_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom) :
    0 ≤ M.pairwiseDobrushinCoefficient a b := by
  unfold pairwiseDobrushinCoefficient
  exact mul_nonneg (by positivity) (M.pairwiseInfluence_nonneg a b)

theorem pairwiseDobrushinCoefficient_eq_zero_of_not_mem_atomInteractionNeighborhood
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    (hb : b ∉ M.atomInteractionNeighborhood a) :
    M.pairwiseDobrushinCoefficient a b = 0 := by
  unfold pairwiseDobrushinCoefficient
  rw [M.pairwiseInfluence_eq_zero_of_not_mem_atomInteractionNeighborhood a b hb]
  ring

theorem singletonKernelTrueSensitivity_triangle
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ ξ₃ : BoundaryCondition Atom) :
    M.singletonKernelTrueSensitivity a ξ₁ ξ₃ ≤
      M.singletonKernelTrueSensitivity a ξ₁ ξ₂ +
        M.singletonKernelTrueSensitivity a ξ₂ ξ₃ := by
  unfold singletonKernelTrueSensitivity
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (abs_sub_le (M.singletonKernelTrueProb a ξ₁)
      (M.singletonKernelTrueProb a ξ₂) (M.singletonKernelTrueProb a ξ₃))

theorem singletonKernelBernoulliL1Sensitivity_triangle
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (ξ₁ ξ₂ ξ₃ : BoundaryCondition Atom) :
    M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₃ ≤
      M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ +
        M.singletonKernelBernoulliL1Sensitivity a ξ₂ ξ₃ := by
  rw [M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity a ξ₁ ξ₃,
    M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity a ξ₁ ξ₂,
    M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity a ξ₂ ξ₃]
  have htri := M.singletonKernelTrueSensitivity_triangle a ξ₁ ξ₂ ξ₃
  nlinarith

theorem singletonKernelBernoulliL1Sensitivity_le_sum_pairwiseDobrushinCoefficient_of_agreesOutside
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (Δ : Finset Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : ∀ c, c ∉ Δ → ξ₁ c = ξ₂ c) :
    M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ ≤
      Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b) := by
  classical
  induction Δ using Finset.induction_on generalizing ξ₁ ξ₂ with
  | empty =>
      have hEq : ξ₁ = ξ₂ := by
        funext c
        exact hag c (by simp)
      simp [singletonKernelBernoulliL1Sensitivity, hEq]
  | @insert b s hb ih =>
      let ξmid : BoundaryCondition Atom := fun c => if c = b then ξ₂ c else ξ₁ c
      have hmid_atom : AgreesOffAtom b ξ₁ ξmid := by
        intro c hc
        simp [ξmid, hc]
      have hmid_out : ∀ c, c ∉ s → ξmid c = ξ₂ c := by
        intro c hcNotS
        by_cases hcEq : c = b
        · simp [ξmid, hcEq]
        · have hcNotInsert : c ∉ insert b s := by
            simp [hcEq, hcNotS]
          calc
            ξmid c = ξ₁ c := by simp [ξmid, hcEq]
            _ = ξ₂ c := hag c hcNotInsert
      calc
        M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξ₂ ≤
            M.singletonKernelBernoulliL1Sensitivity a ξ₁ ξmid +
              M.singletonKernelBernoulliL1Sensitivity a ξmid ξ₂ := by
                exact M.singletonKernelBernoulliL1Sensitivity_triangle a ξ₁ ξmid ξ₂
        _ ≤ M.pairwiseDobrushinCoefficient a b +
              Finset.sum s (fun c => M.pairwiseDobrushinCoefficient a c) := by
                exact add_le_add
                  (M.singletonKernelBernoulliL1Sensitivity_le_pairwiseDobrushinCoefficient a b hmid_atom)
                  (ih hmid_out)
        _ = Finset.sum (insert b s) (fun c => M.pairwiseDobrushinCoefficient a c) := by
              simp [Finset.sum_insert, hb]

theorem singletonKernelBernoulliL1Sensitivity_patch_le_sum_pairwiseDobrushinCoefficient
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    (Δ : Finset Atom)
    (x y : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    M.singletonKernelBernoulliL1Sensitivity a (patch Δ x ξ) (patch Δ y ξ) ≤
      Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b) := by
  refine M.singletonKernelBernoulliL1Sensitivity_le_sum_pairwiseDobrushinCoefficient_of_agreesOutside
    a Δ ?_
  intro c hc
  rw [patch_outside_region Δ x ξ hc, patch_outside_region Δ y ξ hc]

/-- The finite set of sites in `Δ` where two local assignments disagree. -/
def disagreementRegion
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ) : Finset Atom :=
  Δ.filter fun b => if h : b ∈ Δ then x ⟨b, h⟩ ≠ y ⟨b, h⟩ else False

theorem mem_disagreementRegion_iff
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    {b : Atom} :
    b ∈ disagreementRegion x y ↔
      ∃ hb : b ∈ Δ, x ⟨b, hb⟩ ≠ y ⟨b, hb⟩ := by
  unfold disagreementRegion
  constructor
  · intro hb
    rcases Finset.mem_filter.mp hb with ⟨hbΔ, hneq⟩
    refine ⟨hbΔ, ?_⟩
    simpa [hbΔ] using hneq
  · rintro ⟨hbΔ, hneq⟩
    refine Finset.mem_filter.mpr ⟨hbΔ, ?_⟩
    simpa [hbΔ] using hneq

theorem patch_agreesOutside_disagreementRegion
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    ∀ c, c ∉ disagreementRegion x y →
      patch Δ x ξ c = patch Δ y ξ c := by
  intro c hc
  by_cases hcΔ : c ∈ Δ
  · have hxy : x ⟨c, hcΔ⟩ = y ⟨c, hcΔ⟩ := by
      by_contra hneq
      exact hc ((mem_disagreementRegion_iff x y).2 ⟨hcΔ, hneq⟩)
    rw [patch_on_region Δ x ξ hcΔ, patch_on_region Δ y ξ hcΔ, hxy]
  · rw [patch_outside_region Δ x ξ hcΔ, patch_outside_region Δ y ξ hcΔ]

theorem singletonKernelBernoulliL1Sensitivity_patch_le_sum_pairwiseDobrushinCoefficient_disagreementRegion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    M.singletonKernelBernoulliL1Sensitivity a (patch Δ x ξ) (patch Δ y ξ) ≤
      Finset.sum (disagreementRegion x y) (fun b => M.pairwiseDobrushinCoefficient a b) := by
  refine M.singletonKernelBernoulliL1Sensitivity_le_sum_pairwiseDobrushinCoefficient_of_agreesOutside
    a (disagreementRegion x y) ?_
  exact patch_agreesOutside_disagreementRegion x y ξ

theorem singletonKernelBernoulliL1Sensitivity_patch_le_pairwiseDobrushinCoefficient_of_disagreementRegion_subset_singleton
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a b : Atom)
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom)
    (hsub : disagreementRegion x y ⊆ ({b} : Finset Atom)) :
    M.singletonKernelBernoulliL1Sensitivity a (patch Δ x ξ) (patch Δ y ξ) ≤
      M.pairwiseDobrushinCoefficient a b := by
  have hmain :=
    M.singletonKernelBernoulliL1Sensitivity_patch_le_sum_pairwiseDobrushinCoefficient_disagreementRegion
      a x y ξ
  have hsum_le :
      Finset.sum (disagreementRegion x y) (fun c => M.pairwiseDobrushinCoefficient a c) ≤
        Finset.sum ({b} : Finset Atom) (fun c => M.pairwiseDobrushinCoefficient a c) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro c hc_single hc_not_mem
    exact M.pairwiseDobrushinCoefficient_nonneg a c
  have hsingleton :
      Finset.sum ({b} : Finset Atom) (fun c => M.pairwiseDobrushinCoefficient a c) =
        M.pairwiseDobrushinCoefficient a b := by
    simp
  exact le_trans hmain (le_trans hsum_le (by rw [hsingleton]))

/-- Sitewise disagreement indicator of two local assignments, viewed as a real-valued
vector on the ambient atom type. -/
def disagreementIndicator
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ) : Atom → ℝ :=
  fun a => if a ∈ disagreementRegion x y then 1 else 0

theorem disagreementIndicator_nonneg
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    (a : Atom) :
    0 ≤ disagreementIndicator x y a := by
  unfold disagreementIndicator
  split_ifs <;> norm_num

/-- Sup seminorm of a real-valued vector restricted to a finite region. -/
noncomputable def finiteRegionSupSeminorm
    (Λ : Finset Atom)
    (d : Atom → ℝ) : ℝ :=
  if h : Λ.Nonempty then Λ.sup' h d else 0

omit [DecidableEq Atom] in
theorem le_finiteRegionSupSeminorm
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    {a : Atom}
    (ha : a ∈ Λ) :
    d a ≤ finiteRegionSupSeminorm Λ d := by
  by_cases hΛ : Λ.Nonempty
  · simpa [finiteRegionSupSeminorm, hΛ] using (Finset.le_sup' d ha)
  · exact (hΛ ⟨a, ha⟩).elim

omit [DecidableEq Atom] in
theorem finiteRegionSupSeminorm_nonneg
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hd_nonneg : ∀ a ∈ Λ, 0 ≤ d a) :
    0 ≤ finiteRegionSupSeminorm Λ d := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha⟩ := hΛ
    exact le_trans (hd_nonneg a ha) (le_finiteRegionSupSeminorm ha)
  · simp [finiteRegionSupSeminorm, hΛ]

omit [DecidableEq Atom] in
theorem finiteRegionSupSeminorm_mono
    {Λ : Finset Atom}
    {d₁ d₂ : Atom → ℝ}
    (hmono : ∀ a ∈ Λ, d₁ a ≤ d₂ a) :
    finiteRegionSupSeminorm Λ d₁ ≤ finiteRegionSupSeminorm Λ d₂ := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΛ d₁
    rw [finiteRegionSupSeminorm, dif_pos hΛ, hsup]
    exact le_trans (hmono a ha) (le_finiteRegionSupSeminorm (Λ := Λ) (d := d₂) ha)
  · simp [finiteRegionSupSeminorm, hΛ]

/-- The finite-region linear operator associated to the Dobrushin interaction matrix. -/
noncomputable def pairwiseDobrushinOperator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Finset Atom)
    (d : Atom → ℝ) : Atom → ℝ :=
  fun a => Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b * d b)

theorem pairwiseDobrushinOperator_mono
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Finset Atom}
    {d₁ d₂ : Atom → ℝ}
    (hmono : ∀ b ∈ Λ, d₁ b ≤ d₂ b)
    (a : Atom) :
    M.pairwiseDobrushinOperator Λ d₁ a ≤
      M.pairwiseDobrushinOperator Λ d₂ a := by
  unfold pairwiseDobrushinOperator
  refine Finset.sum_le_sum ?_
  intro b hb
  exact mul_le_mul_of_nonneg_left
    (hmono b hb)
    (M.pairwiseDobrushinCoefficient_nonneg a b)

theorem singletonKernelBernoulliL1Sensitivity_patch_le_pairwiseDobrushinOperator_disagreementIndicator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (a : Atom)
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    M.singletonKernelBernoulliL1Sensitivity a (patch Δ x ξ) (patch Δ y ξ) ≤
      M.pairwiseDobrushinOperator Δ (disagreementIndicator x y) a := by
  have hmain :=
    M.singletonKernelBernoulliL1Sensitivity_patch_le_sum_pairwiseDobrushinCoefficient_disagreementRegion
      a x y ξ
  have hsum :
      Finset.sum (disagreementRegion x y) (fun b => M.pairwiseDobrushinCoefficient a b) =
        M.pairwiseDobrushinOperator Δ (disagreementIndicator x y) a := by
    unfold pairwiseDobrushinOperator
    rw [disagreementRegion, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b hbΔ
    by_cases hneq : x ⟨b, hbΔ⟩ ≠ y ⟨b, hbΔ⟩
    · have hmem : b ∈ disagreementRegion x y := by
        exact (mem_disagreementRegion_iff x y).2 ⟨hbΔ, hneq⟩
      simp [disagreementIndicator, hmem, hbΔ, hneq]
    · have hnot : b ∉ disagreementRegion x y := by
        intro hmem
        exact hneq ((mem_disagreementRegion_iff x y).1 hmem).2
      simp [disagreementIndicator, hnot, hbΔ, hneq]
  exact hmain.trans_eq hsum

theorem pairwiseDobrushinOperator_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hd_nonneg : ∀ b ∈ Λ, 0 ≤ d b)
    (a : Atom) :
    0 ≤ M.pairwiseDobrushinOperator Λ d a := by
  unfold pairwiseDobrushinOperator
  exact Finset.sum_nonneg fun b hb =>
    mul_nonneg (M.pairwiseDobrushinCoefficient_nonneg a b) (hd_nonneg b hb)

theorem pairwiseDobrushinOperator_le_rowSum_mul_finiteRegionSupSeminorm
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (a : Atom) :
    M.pairwiseDobrushinOperator Λ d a ≤
      Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) *
        finiteRegionSupSeminorm Λ d := by
  unfold pairwiseDobrushinOperator
  have hsum_le :
      Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b * d b) ≤
        Finset.sum Λ (fun b =>
          M.pairwiseDobrushinCoefficient a b * finiteRegionSupSeminorm Λ d) := by
    refine Finset.sum_le_sum ?_
    intro b hb
    exact mul_le_mul_of_nonneg_left
      (le_finiteRegionSupSeminorm hb)
      (M.pairwiseDobrushinCoefficient_nonneg a b)
  refine le_trans hsum_le ?_
  rw [Finset.sum_mul]

/-- The finite-region contraction constant of the Dobrushin matrix. -/
noncomputable def finiteRegionPairwiseDobrushinConstant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Finset Atom) : ℝ :=
  finiteRegionSupSeminorm Λ (fun a => Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b))

theorem finiteRegionSupSeminorm_pairwiseDobrushinOperator_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hd_nonneg : ∀ b ∈ Λ, 0 ≤ d b) :
    finiteRegionSupSeminorm Λ (M.pairwiseDobrushinOperator Λ d) ≤
      M.finiteRegionPairwiseDobrushinConstant Λ * finiteRegionSupSeminorm Λ d := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΛ (M.pairwiseDobrushinOperator Λ d)
    rw [finiteRegionSupSeminorm, dif_pos hΛ, hsup]
    refine le_trans (M.pairwiseDobrushinOperator_le_rowSum_mul_finiteRegionSupSeminorm a) ?_
    have hrow_le :
        Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) ≤
          M.finiteRegionPairwiseDobrushinConstant Λ := by
      exact le_finiteRegionSupSeminorm
        (Λ := Λ)
        (d := fun a => Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b))
        ha
    exact mul_le_mul_of_nonneg_right hrow_le
      (finiteRegionSupSeminorm_nonneg hd_nonneg)
  · simp [finiteRegionSupSeminorm, finiteRegionPairwiseDobrushinConstant, hΛ]

/-- The finite-region vector of one-site Bernoulli update discrepancies induced by
two patched local assignments. -/
noncomputable def finiteRegionBernoulliUpdateSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) : Atom → ℝ :=
  fun a => M.singletonKernelBernoulliL1Sensitivity a (patch Δ x ξ) (patch Δ y ξ)

theorem finiteRegionBernoulliUpdateSensitivity_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ)
    (a : Atom) :
    0 ≤ M.finiteRegionBernoulliUpdateSensitivity ξ x y a := by
  have htrue :
      0 ≤ M.singletonKernelTrueSensitivity a (patch Δ x ξ) (patch Δ y ξ) :=
    M.singletonKernelTrueSensitivity_nonneg a (patch Δ x ξ) (patch Δ y ξ)
  rw [finiteRegionBernoulliUpdateSensitivity,
    M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity]
  nlinarith

theorem finiteRegionBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ)
    (a : Atom) :
    M.finiteRegionBernoulliUpdateSensitivity ξ x y a ≤
      M.pairwiseDobrushinOperator Δ (disagreementIndicator x y) a := by
  simpa [finiteRegionBernoulliUpdateSensitivity] using
    M.singletonKernelBernoulliL1Sensitivity_patch_le_pairwiseDobrushinOperator_disagreementIndicator
      a x y ξ

theorem finiteRegionSupSeminorm_disagreementIndicator_le_one
    {Δ : Finset Atom}
    (x y : LocalAssignment Atom Δ) :
    finiteRegionSupSeminorm Δ (disagreementIndicator x y) ≤ 1 := by
  by_cases hΔ : Δ.Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΔ (disagreementIndicator x y)
    rw [finiteRegionSupSeminorm, dif_pos hΔ, hsup]
    unfold disagreementIndicator
    split_ifs <;> norm_num
  · simp [finiteRegionSupSeminorm, hΔ]

theorem finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    finiteRegionSupSeminorm Δ (M.finiteRegionBernoulliUpdateSensitivity ξ x y) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ (disagreementIndicator x y) := by
  have hpoint :
      ∀ a ∈ Δ,
        M.finiteRegionBernoulliUpdateSensitivity ξ x y a ≤
          M.pairwiseDobrushinOperator Δ (disagreementIndicator x y) a := by
    intro a ha
    exact M.finiteRegionBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator ξ x y a
  refine le_trans
    (finiteRegionSupSeminorm_mono
      (Λ := Δ)
      (d₁ := M.finiteRegionBernoulliUpdateSensitivity ξ x y)
      (d₂ := M.pairwiseDobrushinOperator Δ (disagreementIndicator x y))
      hpoint)
    ?_
  refine M.finiteRegionSupSeminorm_pairwiseDobrushinOperator_le ?_
  intro b hb
  exact disagreementIndicator_nonneg x y b

theorem paperSmallTotalInfluence_iff_pairwiseDobrushinRowSums_lt_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    M.PaperSmallTotalInfluence ↔
      ∀ a : Atom,
        Finset.sum (M.atomInteractionNeighborhood a)
          (fun b => M.pairwiseDobrushinCoefficient a b) < 1 := by
  constructor
  · intro h a
    let s :=
      Finset.sum (M.atomInteractionNeighborhood a) (fun b => M.pairwiseInfluence a b)
    have hs_nonneg : 0 ≤ s := by
      unfold s
      exact Finset.sum_nonneg fun b hb => M.pairwiseInfluence_nonneg a b
    have hs_lt_two : s < 2 := by
      exact (M.paperSmallTotalInfluence_iff_pairwiseRowSums_lt_two).1 h a
    have hhalf : (1 / 2 : ℝ) * s < 1 := by
      nlinarith
    calc
      Finset.sum (M.atomInteractionNeighborhood a)
          (fun b => M.pairwiseDobrushinCoefficient a b)
        = (1 / 2 : ℝ) * s := by
            unfold s pairwiseDobrushinCoefficient
            rw [Finset.mul_sum]
      _ < 1 := hhalf
  · intro h
    refine (M.paperSmallTotalInfluence_iff_pairwiseRowSums_lt_two).2 ?_
    intro a
    let s :=
      Finset.sum (M.atomInteractionNeighborhood a) (fun b => M.pairwiseInfluence a b)
    have hs_nonneg : 0 ≤ s := by
      unfold s
      exact Finset.sum_nonneg fun b hb => M.pairwiseInfluence_nonneg a b
    have hhalf_lt_one :
        (1 / 2 : ℝ) * s < 1 := by
      have := h a
      calc
        (1 / 2 : ℝ) * s
          = Finset.sum (M.atomInteractionNeighborhood a)
              (fun b => M.pairwiseDobrushinCoefficient a b) := by
                unfold s pairwiseDobrushinCoefficient
                rw [Finset.mul_sum]
        _ < 1 := this
    have hs_lt_two : s < 2 := by
      nlinarith
    simpa [s] using hs_lt_two

theorem finiteRegion_pairwiseDobrushinRowSum_lt_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    (Λ : Finset Atom)
    (a : Atom) :
    Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) < 1 := by
  let N := M.atomInteractionNeighborhood a
  have hEq :
      Finset.sum (Λ.filter fun b => b ∈ N) (fun b => M.pairwiseDobrushinCoefficient a b) =
        Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) := by
    refine Finset.sum_subset (by intro b hb; exact (Finset.mem_filter.mp hb).1) ?_
    intro b hbΛ hbNotInter
    have hbNotN : b ∉ N := by
      intro hbN
      exact hbNotInter (Finset.mem_filter.mpr ⟨hbΛ, hbN⟩)
    exact M.pairwiseDobrushinCoefficient_eq_zero_of_not_mem_atomInteractionNeighborhood a b hbNotN
  have hLe :
      Finset.sum (Λ.filter fun b => b ∈ N) (fun b => M.pairwiseDobrushinCoefficient a b) ≤
        Finset.sum N (fun b => M.pairwiseDobrushinCoefficient a b) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (by intro b hb; exact (Finset.mem_filter.mp hb).2) ?_
    intro b hbN hbNotInter
    exact M.pairwiseDobrushinCoefficient_nonneg a b
  have hRow :
      Finset.sum N (fun b => M.pairwiseDobrushinCoefficient a b) < 1 :=
    (M.paperSmallTotalInfluence_iff_pairwiseDobrushinRowSums_lt_one).1 hM a
  exact lt_of_le_of_lt (hEq ▸ hLe) hRow

theorem finiteRegionPairwiseDobrushinConstant_lt_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    (Λ : Finset Atom) :
    M.finiteRegionPairwiseDobrushinConstant Λ < 1 := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΛ
      (fun a => Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b))
    have hrow : Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) < 1 :=
      M.finiteRegion_pairwiseDobrushinRowSum_lt_one hM Λ a
    simpa [finiteRegionPairwiseDobrushinConstant, finiteRegionSupSeminorm, hΛ, hsup] using hrow
  · simp [finiteRegionPairwiseDobrushinConstant, finiteRegionSupSeminorm, hΛ]

theorem finiteRegionPairwiseDobrushinConstant_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Finset Atom) :
    0 ≤ M.finiteRegionPairwiseDobrushinConstant Λ := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha⟩ := hΛ
    exact le_trans
      (show 0 ≤ Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b) by
        exact Finset.sum_nonneg fun b hb => M.pairwiseDobrushinCoefficient_nonneg a b)
      (le_finiteRegionSupSeminorm
        (Λ := Λ)
        (d := fun a => Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b))
        ha)
  · simp [finiteRegionPairwiseDobrushinConstant, finiteRegionSupSeminorm, hΛ]

theorem finiteRegionSupSeminorm_pairwiseDobrushinOperator_lt
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hd_nonneg : ∀ b ∈ Λ, 0 ≤ d b)
    (hd_pos : 0 < finiteRegionSupSeminorm Λ d) :
    finiteRegionSupSeminorm Λ (M.pairwiseDobrushinOperator Λ d) <
      finiteRegionSupSeminorm Λ d := by
  have hle := M.finiteRegionSupSeminorm_pairwiseDobrushinOperator_le hd_nonneg
  have hconst_lt : M.finiteRegionPairwiseDobrushinConstant Λ < 1 :=
    M.finiteRegionPairwiseDobrushinConstant_lt_one hM Λ
  have hmul_lt :
      M.finiteRegionPairwiseDobrushinConstant Λ * finiteRegionSupSeminorm Λ d <
        finiteRegionSupSeminorm Λ d := by
    nlinarith
  exact lt_of_le_of_lt hle hmul_lt

theorem finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_lt_one_of_paperSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    finiteRegionSupSeminorm Δ (M.finiteRegionBernoulliUpdateSensitivity ξ x y) < 1 := by
  have hle :=
    M.finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_le ξ x y
  have hconst_lt : M.finiteRegionPairwiseDobrushinConstant Δ < 1 :=
    M.finiteRegionPairwiseDobrushinConstant_lt_one hM Δ
  have hind_le : finiteRegionSupSeminorm Δ (disagreementIndicator x y) ≤ 1 :=
    finiteRegionSupSeminorm_disagreementIndicator_le_one x y
  have hconst_nonneg : 0 ≤ M.finiteRegionPairwiseDobrushinConstant Δ := by
    have hzero : 0 ≤ finiteRegionPairwiseDobrushinConstant M Δ := by
      by_cases hΔ : Δ.Nonempty
      · obtain ⟨a, ha⟩ := hΔ
        exact le_trans
          (show 0 ≤ Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b) by
            exact Finset.sum_nonneg fun b hb => M.pairwiseDobrushinCoefficient_nonneg a b)
          (le_finiteRegionSupSeminorm
            (Λ := Δ)
            (d := fun a => Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b))
            ha)
      · simp [finiteRegionPairwiseDobrushinConstant, finiteRegionSupSeminorm, hΔ]
    simpa using hzero
  have hmul_le :
      M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ (disagreementIndicator x y) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ := by
    exact mul_le_of_le_one_right hconst_nonneg hind_le
  have hle' :
      finiteRegionSupSeminorm Δ (M.finiteRegionBernoulliUpdateSensitivity ξ x y) ≤
        M.finiteRegionPairwiseDobrushinConstant Δ := by
    exact le_trans hle hmul_le
  exact lt_of_le_of_lt hle' hconst_lt

theorem finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_le_constant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    finiteRegionSupSeminorm Δ (M.finiteRegionBernoulliUpdateSensitivity ξ x y) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ := by
  have hle :=
    M.finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_le ξ x y
  have hind_le : finiteRegionSupSeminorm Δ (disagreementIndicator x y) ≤ 1 :=
    finiteRegionSupSeminorm_disagreementIndicator_le_one x y
  have hconst_nonneg : 0 ≤ M.finiteRegionPairwiseDobrushinConstant Δ :=
    M.finiteRegionPairwiseDobrushinConstant_nonneg Δ
  have hmul_le :
      M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ (disagreementIndicator x y) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ := by
    exact mul_le_of_le_one_right hconst_nonneg hind_le
  exact le_trans hle hmul_le

theorem sum_toReal_eq_one_of_pmf
    {α : Type*} [Fintype α]
    (q : PMF α) :
    ∑ x, ENNReal.toReal (q x) = 1 := by
  classical
  have hsum : (∑ x : α, q x) = 1 := by
    simpa [tsum_fintype] using (q.tsum_coe : (∑' x : α, q x) = 1)
  have htoReal :
      ENNReal.toReal (∑ x : α, q x) = ∑ x : α, ENNReal.toReal (q x) := by
    simpa using
      (ENNReal.toReal_sum (s := (Finset.univ : Finset α)) (f := fun x => q x) (by
        intro x hx
        simpa using q.apply_ne_top x))
  calc
    ∑ x : α, ENNReal.toReal (q x) = ENNReal.toReal (∑ x : α, q x) := by
      simpa using htoReal.symm
    _ = ENNReal.toReal (1 : ENNReal) := by simp [hsum]
    _ = 1 := by simp

theorem sum_mul_toReal_map_fst_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (q : PMF (α × β))
    (f : α → ℝ) :
    (∑ z : α × β, f z.1 * ENNReal.toReal (q z)) =
      ∑ x : α, f x * ENNReal.toReal ((q.map Prod.fst) x) := by
  classical
  calc
    (∑ z : α × β, f z.1 * ENNReal.toReal (q z))
      = ∑ x : α, ∑ y : β, f x * ENNReal.toReal (q (x, y)) := by
          simp [Fintype.sum_prod_type]
    _ = ∑ x : α, f x * ∑ y : β, ENNReal.toReal (q (x, y)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.mul_sum]
    _ = ∑ x : α, f x * ENNReal.toReal ((q.map Prod.fst) x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          congr 1
          symm
          rw [PMF.map_apply, tsum_fintype]
          rw [ENNReal.toReal_sum]
          · rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
            · simp
            · intro x' hx' hxne
              simp [hxne.symm]
          · intro a ha
            by_cases h : x = a.1
            · simp [h, q.apply_ne_top]
            · simp [h]

theorem sum_mul_toReal_map_snd_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (q : PMF (α × β))
    (g : β → ℝ) :
    (∑ z : α × β, g z.2 * ENNReal.toReal (q z)) =
      ∑ y : β, g y * ENNReal.toReal ((q.map Prod.snd) y) := by
  classical
  calc
    (∑ z : α × β, g z.2 * ENNReal.toReal (q z))
      = ∑ y : β, ∑ x : α, g y * ENNReal.toReal (q (x, y)) := by
          rw [Finset.sum_comm]
          simp [Fintype.sum_prod_type]
    _ = ∑ y : β, g y * ∑ x : α, ENNReal.toReal (q (x, y)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.mul_sum]
    _ = ∑ y : β, g y * ENNReal.toReal ((q.map Prod.snd) y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          congr 1
          symm
          rw [PMF.map_apply, tsum_fintype]
          rw [ENNReal.toReal_sum]
          · rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
            · simp
            · intro y' hy' hyne
              simp [hyne.symm]
          · intro a ha
            by_cases h : y = a.2
            · simp [h, q.apply_ne_top]
            · simp [h]

theorem abs_sub_le_sum_mul_abs_of_pmfCoupling
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (q : PMF (α × β))
    (f : α → ℝ)
    (g : β → ℝ) :
    |(∑ x : α, f x * ENNReal.toReal ((q.map Prod.fst) x)) -
        (∑ y : β, g y * ENNReal.toReal ((q.map Prod.snd) y))| ≤
      ∑ z : α × β, |f z.1 - g z.2| * ENNReal.toReal (q z) := by
  calc
    |(∑ x : α, f x * ENNReal.toReal ((q.map Prod.fst) x)) -
        (∑ y : β, g y * ENNReal.toReal ((q.map Prod.snd) y))|
      = |(∑ z : α × β, f z.1 * ENNReal.toReal (q z)) -
          (∑ z : α × β, g z.2 * ENNReal.toReal (q z))| := by
            rw [sum_mul_toReal_map_fst_eq (q := q) (f := f),
              sum_mul_toReal_map_snd_eq (q := q) (g := g)]
    _ = |∑ z : α × β,
          ((f z.1 - g z.2) * ENNReal.toReal (q z))| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro z hz
            ring
    _ ≤ ∑ z : α × β, |(f z.1 - g z.2) * ENNReal.toReal (q z)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : α × β, |f z.1 - g z.2| * ENNReal.toReal (q z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

/-- Expected one-site Bernoulli update discrepancy under a finite coupling of
two local assignment laws on `Δ`. -/
noncomputable def finiteRegionCouplingExpectedBernoulliUpdateSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) : Atom → ℝ :=
  fun a => ∑ z, M.finiteRegionBernoulliUpdateSensitivity ξ z.1 z.2 a * ENNReal.toReal (q z)

/-- Expected sitewise disagreement vector under a finite coupling of local assignments. -/
noncomputable def finiteRegionCouplingExpectedDisagreement
    {Atom : Type*} [DecidableEq Atom]
    {Δ : Finset Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) : Atom → ℝ :=
  fun a => ∑ z, disagreementIndicator z.1 z.2 a * ENNReal.toReal (q z)

theorem finiteRegionCouplingExpectedBernoulliUpdateSensitivity_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) :
    0 ≤ M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a := by
  unfold finiteRegionCouplingExpectedBernoulliUpdateSensitivity
  exact Finset.sum_nonneg fun z hz =>
    mul_nonneg
      (M.finiteRegionBernoulliUpdateSensitivity_nonneg ξ z.1 z.2 a)
      ENNReal.toReal_nonneg

theorem finiteRegionCouplingExpectedDisagreement_nonneg
    {Atom : Type*} [DecidableEq Atom]
    {Δ : Finset Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) :
    0 ≤ finiteRegionCouplingExpectedDisagreement q a := by
  unfold finiteRegionCouplingExpectedDisagreement
  exact Finset.sum_nonneg fun z hz =>
    mul_nonneg
      (disagreementIndicator_nonneg z.1 z.2 a)
      ENNReal.toReal_nonneg

theorem finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) :
    M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a ≤
      M.pairwiseDobrushinOperator Δ (finiteRegionCouplingExpectedDisagreement q) a := by
  unfold finiteRegionCouplingExpectedBernoulliUpdateSensitivity
  unfold finiteRegionCouplingExpectedDisagreement
  unfold pairwiseDobrushinOperator
  calc
    ∑ z,
        M.finiteRegionBernoulliUpdateSensitivity ξ z.1 z.2 a * ENNReal.toReal (q z)
      ≤ ∑ z,
          M.pairwiseDobrushinOperator Δ (disagreementIndicator z.1 z.2) a *
            ENNReal.toReal (q z) := by
            refine Finset.sum_le_sum ?_
            intro z hz
            exact mul_le_mul_of_nonneg_right
              (M.finiteRegionBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator ξ z.1 z.2 a)
              ENNReal.toReal_nonneg
    _ = ∑ z,
          (Finset.sum Δ (fun b =>
            M.pairwiseDobrushinCoefficient a b * disagreementIndicator z.1 z.2 b)) *
              ENNReal.toReal (q z) := by
            rfl
    _ = ∑ z, Finset.sum Δ (fun b =>
          (M.pairwiseDobrushinCoefficient a b * disagreementIndicator z.1 z.2 b) *
            ENNReal.toReal (q z)) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [Finset.sum_mul]
    _ = Finset.sum Δ (fun b => ∑ z,
          (M.pairwiseDobrushinCoefficient a b * disagreementIndicator z.1 z.2 b) *
            ENNReal.toReal (q z)) := by
            rw [Finset.sum_comm]
    _ = Finset.sum Δ (fun b =>
          M.pairwiseDobrushinCoefficient a b *
            (∑ z, disagreementIndicator z.1 z.2 b * ENNReal.toReal (q z))) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ
        (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement q) := by
  have hpoint :
      ∀ a ∈ Δ,
        M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a ≤
          M.pairwiseDobrushinOperator Δ (finiteRegionCouplingExpectedDisagreement q) a := by
    intro a ha
    exact M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator ξ q a
  have hd_nonneg :
      ∀ b ∈ Δ, 0 ≤ finiteRegionCouplingExpectedDisagreement q b := by
    intro b hb
    exact finiteRegionCouplingExpectedDisagreement_nonneg q b
  refine le_trans
    (finiteRegionSupSeminorm_mono
      (Λ := Δ)
      (d₁ := M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q)
      (d₂ := M.pairwiseDobrushinOperator Δ (finiteRegionCouplingExpectedDisagreement q))
      hpoint)
    (M.finiteRegionSupSeminorm_pairwiseDobrushinOperator_le hd_nonneg)

theorem abs_sub_le_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_of_pmfCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) :
    |(∑ x : LocalAssignment Atom Δ,
          M.singletonKernelTrueProb a (patch Δ x ξ) *
            ENNReal.toReal ((q.map Prod.fst) x)) -
        (∑ y : LocalAssignment Atom Δ,
          M.singletonKernelTrueProb a (patch Δ y ξ) *
            ENNReal.toReal ((q.map Prod.snd) y))| ≤
      M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a := by
  have hbase :=
    abs_sub_le_sum_mul_abs_of_pmfCoupling
      (q := q)
      (f := fun x : LocalAssignment Atom Δ => M.singletonKernelTrueProb a (patch Δ x ξ))
      (g := fun y : LocalAssignment Atom Δ => M.singletonKernelTrueProb a (patch Δ y ξ))
  refine le_trans hbase ?_
  unfold finiteRegionCouplingExpectedBernoulliUpdateSensitivity
  refine Finset.sum_le_sum ?_
  intro z hz
  have htrue_le_l1 :
      M.singletonKernelTrueSensitivity a (patch Δ z.1 ξ) (patch Δ z.2 ξ) ≤
        M.singletonKernelBernoulliL1Sensitivity a (patch Δ z.1 ξ) (patch Δ z.2 ξ) := by
    have hnonneg :=
      M.singletonKernelTrueSensitivity_nonneg a (patch Δ z.1 ξ) (patch Δ z.2 ξ)
    rw [M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity
      a (patch Δ z.1 ξ) (patch Δ z.2 ξ)]
    nlinarith
  exact mul_le_mul_of_nonneg_right
    htrue_le_l1
    ENNReal.toReal_nonneg

theorem finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_constant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    {a : Atom}
    (ha : a ∈ Δ) :
    M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a ≤
      M.finiteRegionPairwiseDobrushinConstant Δ := by
  have hsumw :
      ∑ z, ENNReal.toReal (q z) = 1 :=
    sum_toReal_eq_one_of_pmf q
  calc
    M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q a
      = ∑ z,
          M.finiteRegionBernoulliUpdateSensitivity ξ z.1 z.2 a *
            ENNReal.toReal (q z) := by
              rfl
    _ ≤ ∑ z,
          M.finiteRegionPairwiseDobrushinConstant Δ * ENNReal.toReal (q z) := by
            refine Finset.sum_le_sum ?_
            intro z hz
            have hz_le :
                M.finiteRegionBernoulliUpdateSensitivity ξ z.1 z.2 a ≤
                  M.finiteRegionPairwiseDobrushinConstant Δ := by
              exact le_trans
                (le_finiteRegionSupSeminorm (Λ := Δ)
                  (d := M.finiteRegionBernoulliUpdateSensitivity ξ z.1 z.2) ha)
                (M.finiteRegionSupSeminorm_finiteRegionBernoulliUpdateSensitivity_le_constant ξ z.1 z.2)
            exact mul_le_mul_of_nonneg_right hz_le ENNReal.toReal_nonneg
    _ = M.finiteRegionPairwiseDobrushinConstant Δ * ∑ z, ENNReal.toReal (q z) := by
          rw [Finset.mul_sum]
    _ = M.finiteRegionPairwiseDobrushinConstant Δ := by
          rw [hsumw, mul_one]

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_constant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ
        (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ := by
  by_cases hΔ : Δ.Nonempty
  · calc
      finiteRegionSupSeminorm Δ
          (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q)
        ≤ finiteRegionSupSeminorm Δ (fun _ => M.finiteRegionPairwiseDobrushinConstant Δ) := by
            refine finiteRegionSupSeminorm_mono
              (Λ := Δ)
              (d₁ := M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q)
              (d₂ := fun _ => M.finiteRegionPairwiseDobrushinConstant Δ) ?_
            intro a ha
            exact M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_constant ξ q ha
      _ = M.finiteRegionPairwiseDobrushinConstant Δ := by
            simp [finiteRegionSupSeminorm, hΔ, Finset.sup'_const]
  · simp [finiteRegionSupSeminorm, hΔ, M.finiteRegionPairwiseDobrushinConstant_nonneg Δ]

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_lt_one_of_paperSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Δ : Finset Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ
        (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q) < 1 := by
  exact lt_of_le_of_lt
    (M.finiteRegionSupSeminorm_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_constant ξ q)
    (M.finiteRegionPairwiseDobrushinConstant_lt_one hM Δ)

theorem singletonTrueProbability_toReal_eq_boundaryPMFExpectation_of_fixedRegionDLR
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (a : Atom) :
    let J : Region Atom :=
      cylinderBoundarySupportRegion
        M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({a} : Region Atom) ({a} : Region Atom)
    ((μ : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal =
      ∑ x : LocalAssignment Atom J,
        M.singletonKernelTrueProb a (patch J x (fun _ => false)) *
          ENNReal.toReal
            (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let J : Region Atom :=
    cylinderBoundarySupportRegion
      M'.toInfiniteGroundMLNSpec ({a} : Region Atom) ({a} : Region Atom)
  let S : Set (LocalAssignment Atom ({a} : Region Atom)) := singletonTrueAssignmentSet a
  have hS : MeasurableSet S := measurableSet_singletonTrueAssignmentSet a
  have hdlr :
      ∫⁻ ω,
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M' ({a} : Region Atom) ω
          (MeasureTheory.cylinder ({a} : Region Atom) S) ∂ (μ : Measure (InfiniteWorld Atom)) =
        (μ : Measure (InfiniteWorld Atom)) (MeasureTheory.cylinder ({a} : Region Atom) S) := by
    exact hμ ({a} : Region Atom) ({a} : Region Atom) S hS
  have hlim :
      ∫⁻ x,
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
          ({a} : Region Atom) ({a} : Region Atom) S x
          ∂ Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) J =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M' ({a} : Region Atom) ω
            (MeasureTheory.cylinder ({a} : Region Atom) S) ∂ (μ : Measure (InfiniteWorld Atom)) := by
    simpa [J, S] using
      (Mettapedia.Logic.PLNMarkovLogicInfiniteFixedRegionDLR.RegionExhaustion.limitMarginal_lintegral_cylinderBoundaryKernelValue
        M' (μ : Measure (InfiniteWorld Atom))
        ({a} : Region Atom) ({a} : Region Atom) S hS)
  have hEq :
      (μ : Measure (InfiniteWorld Atom)) (MeasureTheory.cylinder ({a} : Region Atom) S) =
        ∑ x : LocalAssignment Atom J,
          StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
            ({a} : Region Atom) ({a} : Region Atom) S x *
              (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
    calc
      (μ : Measure (InfiniteWorld Atom)) (MeasureTheory.cylinder ({a} : Region Atom) S)
        = ∫⁻ x,
            StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
              ({a} : Region Atom) ({a} : Region Atom) S x
              ∂ Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) J := by
                exact Eq.symm (hlim.trans hdlr)
      _ = ∑ x : LocalAssignment Atom J,
            StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
              ({a} : Region Atom) ({a} : Region Atom) S x *
                (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                  (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
                rw [MeasureTheory.lintegral_fintype]
                simp [Measure.toPMF_apply]
  have hne_top :
      ∀ x : LocalAssignment Atom J,
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
          ({a} : Region Atom) ({a} : Region Atom) S x *
            (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) ≠ (⊤ : ENNReal) := by
    intro x
    exact ENNReal.mul_ne_top
      (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue_ne_top
        M' ({a} : Region Atom) ({a} : Region Atom) S x)
      ((((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) J).toPMF)).apply_ne_top x)
  calc
    ((μ : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) S)).toReal
      = ENNReal.toReal
          (∑ x : LocalAssignment Atom J,
            StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
              ({a} : Region Atom) ({a} : Region Atom) S x *
                (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                  (μ : Measure (InfiniteWorld Atom)) J).toPMF) x)) := by
                  simp [hEq]
    _ = ∑ x : LocalAssignment Atom J,
          ENNReal.toReal
            (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
              ({a} : Region Atom) ({a} : Region Atom) S x *
                (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                  (μ : Measure (InfiniteWorld Atom)) J).toPMF) x)) := by
                  rw [ENNReal.toReal_sum]
                  intro x hx
                  exact hne_top x
    _ = ∑ x : LocalAssignment Atom J,
          M.singletonKernelTrueProb a (patch J x (fun _ => false)) *
            ENNReal.toReal
              (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              calc
                ENNReal.toReal
                    (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
                      ({a} : Region Atom) ({a} : Region Atom) S x *
                      (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                        (μ : Measure (InfiniteWorld Atom)) J).toPMF) x))
                  =
                    ENNReal.toReal
                      (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M'
                        ({a} : Region Atom) ({a} : Region Atom) S x) *
                    ENNReal.toReal
                      (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                        (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
                          rw [ENNReal.toReal_mul]
                _ =
                    M.singletonKernelTrueProb a (patch J x (fun _ => false)) *
                    ENNReal.toReal
                      (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                        (μ : Measure (InfiniteWorld Atom)) J).toPMF) x) := by
                          simp [M', J, S, ClassicalInfiniteGroundMLNSpec.singletonKernelTrueProb,
                            StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue]

theorem singletonTrueProbability_discrepancy_le_of_limitMarginalCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (a : Atom)
    (q : PMF
      (LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom)) ×
       LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom))))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF) :
    |((μ : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal -
      ((ν : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal| ≤
      M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity (fun _ => false) q a := by
  let J : Region Atom :=
    cylinderBoundarySupportRegion
      M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
      ({a} : Region Atom) ({a} : Region Atom)
  have hμ' :
      ((μ : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal =
        ∑ x : LocalAssignment Atom J,
          M.singletonKernelTrueProb a (patch J x (fun _ => false)) *
            ENNReal.toReal ((q.map Prod.fst) x) := by
    simpa [J, hqfst] using
      (M.singletonTrueProbability_toReal_eq_boundaryPMFExpectation_of_fixedRegionDLR μ hμ a)
  have hν' :
      ((ν : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal =
        ∑ y : LocalAssignment Atom J,
          M.singletonKernelTrueProb a (patch J y (fun _ => false)) *
            ENNReal.toReal ((q.map Prod.snd) y) := by
    simpa [J, hqsnd] using
      (M.singletonTrueProbability_toReal_eq_boundaryPMFExpectation_of_fixedRegionDLR ν hν a)
  calc
    |((μ : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal -
      ((ν : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal|
      = |(∑ x : LocalAssignment Atom J,
            M.singletonKernelTrueProb a (patch J x (fun _ => false)) *
              ENNReal.toReal ((q.map Prod.fst) x)) -
          (∑ y : LocalAssignment Atom J,
            M.singletonKernelTrueProb a (patch J y (fun _ => false)) *
              ENNReal.toReal ((q.map Prod.snd) y))| := by
              rw [hμ', hν']
    _ ≤ M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity (fun _ => false) q a := by
          exact M.abs_sub_le_finiteRegionCouplingExpectedBernoulliUpdateSensitivity_of_pmfCoupling
            (ξ := fun _ => false) q a

/-- Singleton true-cylinder discrepancy between two candidate global measures. -/
noncomputable def singletonTrueProbabilityDiscrepancy
    (_M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom)) : Atom → ℝ :=
  fun a =>
    |((μ : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal -
      ((ν : Measure (InfiniteWorld Atom))
        (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal|

theorem singletonTrueProbabilityDiscrepancy_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (a : Atom) :
    0 ≤ M.singletonTrueProbabilityDiscrepancy μ ν a := by
  unfold singletonTrueProbabilityDiscrepancy
  exact abs_nonneg _

/-- Real-valued indicator of a finite-region assignment event. -/
noncomputable def finiteRegionEventIndicator
    {Δ : Region Atom}
    (S : Set (LocalAssignment Atom Δ)) :
    LocalAssignment Atom Δ → ℝ := by
  classical
  exact fun x => if x ∈ S then 1 else 0

/-- Finite-region event probability read from the limiting marginal. -/
noncomputable def finiteRegionSetProbability
    (_M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) : ℝ :=
  (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ) S)).toReal

/-- Finite-region event discrepancy between two candidate global measures. -/
noncomputable def finiteRegionSetProbabilityDiscrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) : ℝ :=
  |M.finiteRegionSetProbability μ Δ S - M.finiteRegionSetProbability ν Δ S|

/-- Pointwise finite-region assignment probability discrepancy. -/
noncomputable def finiteRegionAssignmentProbabilityDiscrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (x : LocalAssignment Atom Δ) : ℝ :=
  M.finiteRegionSetProbabilityDiscrepancy μ ν Δ ({x} : Set (LocalAssignment Atom Δ))

/-- The finite-region `L1` discrepancy of the assignment marginals. -/
noncomputable def finiteRegionAssignmentL1Discrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom) : ℝ :=
  ∑ x : LocalAssignment Atom Δ, M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x

/-- The finite-region total-variation-style discrepancy of the assignment marginals. -/
noncomputable def finiteRegionAssignmentTotalVariation
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom) : ℝ :=
  (1 / 2 : ℝ) * M.finiteRegionAssignmentL1Discrepancy μ ν Δ

/-- Expected indicator mismatch of a finite-region event under a coupling. -/
noncomputable def finiteRegionCouplingExpectedEventDisagreement
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (S : Set (LocalAssignment Atom Δ)) : ℝ :=
  ∑ z, |finiteRegionEventIndicator (Atom := Atom) S z.1 -
      finiteRegionEventIndicator (Atom := Atom) S z.2| * ENNReal.toReal (q z)

theorem finiteRegionSetProbability_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    0 ≤ M.finiteRegionSetProbability μ Δ S := by
  unfold finiteRegionSetProbability
  exact ENNReal.toReal_nonneg

theorem finiteRegionSetProbabilityDiscrepancy_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    0 ≤ M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S := by
  unfold finiteRegionSetProbabilityDiscrepancy
  exact abs_nonneg _

theorem finiteRegionAssignmentProbabilityDiscrepancy_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (x : LocalAssignment Atom Δ) :
    0 ≤ M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x := by
  exact M.finiteRegionSetProbabilityDiscrepancy_nonneg μ ν Δ ({x} : Set (LocalAssignment Atom Δ))

theorem finiteRegionAssignmentL1Discrepancy_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom) :
    0 ≤ M.finiteRegionAssignmentL1Discrepancy μ ν Δ := by
  unfold finiteRegionAssignmentL1Discrepancy
  exact Finset.sum_nonneg fun x hx =>
    M.finiteRegionAssignmentProbabilityDiscrepancy_nonneg μ ν Δ x

theorem finiteRegionAssignmentTotalVariation_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom) :
    0 ≤ M.finiteRegionAssignmentTotalVariation μ ν Δ := by
  unfold finiteRegionAssignmentTotalVariation
  exact mul_nonneg (by norm_num) (M.finiteRegionAssignmentL1Discrepancy_nonneg μ ν Δ)

theorem finiteRegionSetProbability_eq_sum_indicator_limitMarginal
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    M.finiteRegionSetProbability μ Δ S =
      ∑ x : LocalAssignment Atom Δ,
        finiteRegionEventIndicator (Atom := Atom) S x *
          ENNReal.toReal
            (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) Δ).toPMF) x) := by
  calc
    M.finiteRegionSetProbability μ Δ S
      = ENNReal.toReal
          ((((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) Δ).toPMF).toMeasure) S) := by
              rw [finiteRegionSetProbability, Measure.toPMF_toMeasure]
    _ = ENNReal.toReal
          (∑ x : LocalAssignment Atom Δ,
            S.indicator
              (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)) x) := by
              rw [PMF.toMeasure_apply_fintype]
    _ = ∑ x : LocalAssignment Atom Δ,
          ENNReal.toReal
            (S.indicator
              (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)) x) := by
              rw [ENNReal.toReal_sum]
              intro x hx
              by_cases hxS : x ∈ S
              · simp [Set.indicator, hxS,
                  (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                    (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)).apply_ne_top x]
              · simp [Set.indicator, hxS]
    _ = ∑ x : LocalAssignment Atom Δ,
          finiteRegionEventIndicator (Atom := Atom) S x *
            ENNReal.toReal
              (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ).toPMF) x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hxS : x ∈ S
              · simp [finiteRegionEventIndicator, Set.indicator, hxS]
              · simp [finiteRegionEventIndicator, Set.indicator, hxS]

theorem finiteRegionSetProbabilityDiscrepancy_le_of_limitMarginalCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ))
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) :
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S ≤
      finiteRegionCouplingExpectedEventDisagreement (Atom := Atom) q S := by
  unfold finiteRegionSetProbabilityDiscrepancy finiteRegionCouplingExpectedEventDisagreement
  rw [M.finiteRegionSetProbability_eq_sum_indicator_limitMarginal μ Δ S,
    M.finiteRegionSetProbability_eq_sum_indicator_limitMarginal ν Δ S,
    ← hqfst, ← hqsnd]
  exact abs_sub_le_sum_mul_abs_of_pmfCoupling
    (q := q)
    (f := finiteRegionEventIndicator (Atom := Atom) S)
    (g := finiteRegionEventIndicator (Atom := Atom) S)

/-- Finite-region local-query discrepancy between two candidate global measures. -/
noncomputable def finiteRegionLocalQueryDiscrepancy
    (_M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) : ℝ :=
  |((μ : Measure (InfiniteWorld Atom)) (localQueryEvent Δ q)).toReal -
    ((ν : Measure (InfiniteWorld Atom)) (localQueryEvent Δ q)).toReal|

theorem finiteRegionLocalQueryDiscrepancy_eq_setProbabilityDiscrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q =
      M.finiteRegionSetProbabilityDiscrepancy μ ν Δ (localConstraintSet Δ q) := by
  unfold finiteRegionLocalQueryDiscrepancy finiteRegionSetProbabilityDiscrepancy finiteRegionSetProbability
  rw [Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal_apply_localConstraintSet
      (μ := (μ : Measure (InfiniteWorld Atom))) (Λ := Δ) (q := q),
    Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal_apply_localConstraintSet
      (μ := (ν : Measure (InfiniteWorld Atom))) (Λ := Δ) (q := q)]

theorem finiteRegionLocalQueryDiscrepancy_le_of_limitMarginalCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (qv : LocalConstraintQuery Atom Δ)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ qv ≤
      finiteRegionCouplingExpectedEventDisagreement (Atom := Atom) q (localConstraintSet Δ qv) := by
  rw [M.finiteRegionLocalQueryDiscrepancy_eq_setProbabilityDiscrepancy μ ν Δ qv]
  exact M.finiteRegionSetProbabilityDiscrepancy_le_of_limitMarginalCoupling
    μ ν Δ (localConstraintSet Δ qv) q hqfst hqsnd

theorem finiteRegionAssignmentProbabilityDiscrepancy_eq_abs_sub_limitMarginalToReal
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (x : LocalAssignment Atom Δ) :
    M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x =
      |ENNReal.toReal
          (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) Δ).toPMF) x) -
        ENNReal.toReal
          (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) x)| := by
  unfold finiteRegionAssignmentProbabilityDiscrepancy finiteRegionSetProbabilityDiscrepancy
    finiteRegionSetProbability
  simp [MeasureTheory.Measure.toPMF_apply]

theorem finiteRegionSetProbabilityDiscrepancy_le_assignmentL1Discrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S ≤
      M.finiteRegionAssignmentL1Discrepancy μ ν Δ := by
  let p : LocalAssignment Atom Δ → ℝ := fun x =>
    ENNReal.toReal
      (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF) x)
  let q : LocalAssignment Atom Δ → ℝ := fun x =>
    ENNReal.toReal
      (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) x)
  have hsum :
      |(∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * p x) -
          (∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * q x)| ≤
        ∑ x : LocalAssignment Atom Δ, |p x - q x| := by
    calc
      |(∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * p x) -
          (∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * q x)|
        = |∑ x : LocalAssignment Atom Δ,
              (finiteRegionEventIndicator (Atom := Atom) S x * p x -
                finiteRegionEventIndicator (Atom := Atom) S x * q x)| := by
              rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ x : LocalAssignment Atom Δ,
            |finiteRegionEventIndicator (Atom := Atom) S x * p x -
              finiteRegionEventIndicator (Atom := Atom) S x * q x| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : LocalAssignment Atom Δ, |p x - q x| := by
            refine Finset.sum_le_sum ?_
            intro x hx
            by_cases hxS : x ∈ S
            · simp [finiteRegionEventIndicator, hxS, p, q]
            · simp [finiteRegionEventIndicator, hxS, p, q]
  calc
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S
      = |(∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * p x) -
          (∑ x : LocalAssignment Atom Δ, finiteRegionEventIndicator (Atom := Atom) S x * q x)| := by
            rw [finiteRegionSetProbabilityDiscrepancy,
              M.finiteRegionSetProbability_eq_sum_indicator_limitMarginal μ Δ S,
              M.finiteRegionSetProbability_eq_sum_indicator_limitMarginal ν Δ S]
      _ ≤ ∑ x : LocalAssignment Atom Δ, |p x - q x| := hsum
      _ = M.finiteRegionAssignmentL1Discrepancy μ ν Δ := by
            unfold finiteRegionAssignmentL1Discrepancy
            refine Finset.sum_congr rfl ?_
            intro x hx
            symm
            exact M.finiteRegionAssignmentProbabilityDiscrepancy_eq_abs_sub_limitMarginalToReal μ ν Δ x

theorem finiteRegionLocalQueryDiscrepancy_le_assignmentL1Discrepancy
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤
      M.finiteRegionAssignmentL1Discrepancy μ ν Δ := by
  rw [M.finiteRegionLocalQueryDiscrepancy_eq_setProbabilityDiscrepancy μ ν Δ q]
  exact M.finiteRegionSetProbabilityDiscrepancy_le_assignmentL1Discrepancy
    μ ν Δ (localConstraintSet Δ q)

theorem finiteRegionSetProbabilityDiscrepancy_le_two_mul_assignmentTotalVariation
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S ≤
      2 * M.finiteRegionAssignmentTotalVariation μ ν Δ := by
  calc
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S ≤
        M.finiteRegionAssignmentL1Discrepancy μ ν Δ :=
      M.finiteRegionSetProbabilityDiscrepancy_le_assignmentL1Discrepancy μ ν Δ S
    _ = 2 * M.finiteRegionAssignmentTotalVariation μ ν Δ := by
      unfold finiteRegionAssignmentTotalVariation
      ring

theorem finiteRegionLocalQueryDiscrepancy_le_two_mul_assignmentTotalVariation
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤
      2 * M.finiteRegionAssignmentTotalVariation μ ν Δ := by
  calc
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q ≤
        M.finiteRegionAssignmentL1Discrepancy μ ν Δ :=
      M.finiteRegionLocalQueryDiscrepancy_le_assignmentL1Discrepancy μ ν Δ q
    _ = 2 * M.finiteRegionAssignmentTotalVariation μ ν Δ := by
      unfold finiteRegionAssignmentTotalVariation
      ring

theorem limitMarginal_toPMF_eq_of_assignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (hassign : ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ).toPMF =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν : Measure (InfiniteWorld Atom)) Δ).toPMF := by
  apply PMF.ext
  intro x
  have hsub :
      M.finiteRegionSetProbability μ Δ ({x} : Set (LocalAssignment Atom Δ)) -
        M.finiteRegionSetProbability ν Δ ({x} : Set (LocalAssignment Atom Δ)) = 0 := by
    exact abs_eq_zero.mp (by
      simpa [finiteRegionAssignmentProbabilityDiscrepancy, finiteRegionSetProbabilityDiscrepancy]
        using hassign x)
  have hreal :
      M.finiteRegionSetProbability μ Δ ({x} : Set (LocalAssignment Atom Δ)) =
        M.finiteRegionSetProbability ν Δ ({x} : Set (LocalAssignment Atom Δ)) :=
    sub_eq_zero.mp hsub
  have hmeasure :
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ) ({x} : Set (LocalAssignment Atom Δ)) =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ) ({x} : Set (LocalAssignment Atom Δ)) := by
    exact
      (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top _ _)
        (measure_ne_top _ _)).mp (by
          simpa [finiteRegionSetProbability] using hreal)
  rw [MeasureTheory.Measure.toPMF_apply, MeasureTheory.Measure.toPMF_apply]
  exact hmeasure

theorem limitMarginal_eq_of_assignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (hassign : ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ =
        Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ := by
  have hpmf := M.limitMarginal_toPMF_eq_of_assignmentProbabilityDiscrepancy_eq_zero μ ν Δ hassign
  have hmeasure := congrArg PMF.toMeasure hpmf
  simpa using hmeasure

theorem finiteRegionSetProbability_eq_of_assignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ))
    (hassign : ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    M.finiteRegionSetProbability μ Δ S = M.finiteRegionSetProbability ν Δ S := by
  have hlim := M.limitMarginal_eq_of_assignmentProbabilityDiscrepancy_eq_zero μ ν Δ hassign
  have hset :=
    congrArg (fun ρ : Measure (LocalAssignment Atom Δ) => ENNReal.toReal (ρ S)) hlim
  simpa [finiteRegionSetProbability] using hset

theorem finiteRegionSetProbabilityDiscrepancy_eq_zero_of_assignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (S : Set (LocalAssignment Atom Δ))
    (hassign : ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    M.finiteRegionSetProbabilityDiscrepancy μ ν Δ S = 0 := by
  unfold finiteRegionSetProbabilityDiscrepancy
  rw [M.finiteRegionSetProbability_eq_of_assignmentProbabilityDiscrepancy_eq_zero μ ν Δ S hassign]
  simp

theorem finiteRegionLocalQueryDiscrepancy_eq_zero_of_assignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : LocalConstraintQuery Atom Δ)
    (hassign : ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Δ q = 0 := by
  rw [M.finiteRegionLocalQueryDiscrepancy_eq_setProbabilityDiscrepancy μ ν Δ q]
  exact M.finiteRegionSetProbabilityDiscrepancy_eq_zero_of_assignmentProbabilityDiscrepancy_eq_zero
    μ ν Δ (localConstraintSet Δ q) hassign

theorem eq_of_limitMarginal_eq_all_regions
    (_M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hlim : ∀ Δ : Region Atom,
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ =
          Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν : Measure (InfiniteWorld Atom)) Δ) :
    (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  let P :
      ∀ Δ : Region Atom,
        Measure (LocalAssignment Atom Δ) :=
    Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (Atom := Atom) (μ : Measure (InfiniteWorld Atom))
  have hμP :
      MeasureTheory.IsProjectiveLimit
        (ι := Atom) (α := fun _ : Atom => Bool)
        (μ : Measure (InfiniteWorld Atom)) P := by
    intro Δ
    rfl
  have hνP :
      MeasureTheory.IsProjectiveLimit
        (ι := Atom) (α := fun _ : Atom => Bool)
        (ν : Measure (InfiniteWorld Atom)) P := by
    intro Δ
    simpa [P] using (hlim Δ).symm
  exact MeasureTheory.IsProjectiveLimit.unique
    (ι := Atom) (α := fun _ : Atom => Bool)
    (P := P)
    (μ := (μ : Measure (InfiniteWorld Atom)))
    (ν := (ν : Measure (InfiniteWorld Atom)))
    hμP hνP

theorem eq_of_finiteRegionAssignmentProbabilityDiscrepancy_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hassign : ∀ Δ : Region Atom, ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0) :
    (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  refine M.eq_of_limitMarginal_eq_all_regions μ ν ?_
  intro Δ
  exact M.limitMarginal_eq_of_assignmentProbabilityDiscrepancy_eq_zero μ ν Δ (hassign Δ)

theorem finiteRegionAssignmentProbabilityDiscrepancy_eq_zero_of_totalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (htv : M.finiteRegionAssignmentTotalVariation μ ν Δ = 0) :
    ∀ x : LocalAssignment Atom Δ,
      M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0 := by
  have hl1 : M.finiteRegionAssignmentL1Discrepancy μ ν Δ = 0 := by
    unfold finiteRegionAssignmentTotalVariation at htv
    have hnonneg := M.finiteRegionAssignmentL1Discrepancy_nonneg μ ν Δ
    nlinarith
  have hall :
      ∀ x : LocalAssignment Atom Δ,
        M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0 := by
    have hsum :
        ∑ x : LocalAssignment Atom Δ,
          M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x = 0 := by
      simpa [finiteRegionAssignmentL1Discrepancy] using hl1
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x hx => M.finiteRegionAssignmentProbabilityDiscrepancy_nonneg μ ν Δ x)).1 hsum
    intro x
    exact hzero x (Finset.mem_univ x)
  exact hall

theorem eq_of_finiteRegionAssignmentTotalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (htv : ∀ Δ : Region Atom, M.finiteRegionAssignmentTotalVariation μ ν Δ = 0) :
    (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  refine M.eq_of_finiteRegionAssignmentProbabilityDiscrepancy_eq_zero μ ν ?_
  intro Δ x
  exact M.finiteRegionAssignmentProbabilityDiscrepancy_eq_zero_of_totalVariation_eq_zero
    μ ν Δ (htv Δ) x

theorem singletonTrueProbabilityDiscrepancy_le_pairwiseDobrushinOperator_of_boundarySupportCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (a : Atom)
    (q : PMF
      (LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom)) ×
       LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom))))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF) :
    M.singletonTrueProbabilityDiscrepancy μ ν a ≤
      M.pairwiseDobrushinOperator
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom))
        (finiteRegionCouplingExpectedDisagreement q) a := by
  have hbase' :
      |((μ : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal -
        ((ν : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder ({a} : Region Atom) (singletonTrueAssignmentSet a))).toReal| ≤
        M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity (fun _ => false) q a := by
    exact M.singletonTrueProbability_discrepancy_le_of_limitMarginalCoupling
      μ ν hμ hν a q hqfst hqsnd
  have hbase :
      M.singletonTrueProbabilityDiscrepancy μ ν a ≤
        M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity (fun _ => false) q a := by
    simpa [singletonTrueProbabilityDiscrepancy] using hbase'
  exact le_trans hbase
    (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator
      (ξ := fun _ => false) (q := q) a)

theorem singletonTrueProbabilityDiscrepancy_le_pairwiseDobrushinOperator_of_boundarySupportCoupling_mono
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hν : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)))
    (a : Atom)
    (q : PMF
      (LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom)) ×
       LocalAssignment Atom
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom))))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom))
          (cylinderBoundarySupportRegion
            M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
            ({a} : Region Atom) ({a} : Region Atom))).toPMF)
    {d : Atom → ℝ}
    (hd : ∀ b ∈
      cylinderBoundarySupportRegion
        M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
        ({a} : Region Atom) ({a} : Region Atom),
      finiteRegionCouplingExpectedDisagreement q b ≤ d b) :
    M.singletonTrueProbabilityDiscrepancy μ ν a ≤
      M.pairwiseDobrushinOperator
        (cylinderBoundarySupportRegion
          M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
          ({a} : Region Atom) ({a} : Region Atom)) d a := by
  refine le_trans
    (M.singletonTrueProbabilityDiscrepancy_le_pairwiseDobrushinOperator_of_boundarySupportCoupling
      μ ν hμ hν a q hqfst hqsnd)
    (M.pairwiseDobrushinOperator_mono hd a)

theorem finiteRegion_eq_zero_of_nonneg_le_sum_of_rowSums_lt_one
    {Λ : Finset Atom}
    {c : Atom → Atom → ℝ}
    {d : Atom → ℝ}
    (hc_nonneg : ∀ a b, 0 ≤ c a b)
    (hrows : ∀ a ∈ Λ, Finset.sum Λ (fun b => c a b) < 1)
    (hd_nonneg : ∀ a ∈ Λ, 0 ≤ d a)
    (hd_le : ∀ a ∈ Λ, d a ≤ Finset.sum Λ (fun b => c a b * d b)) :
    ∀ a ∈ Λ, d a = 0 := by
  classical
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨m, hmΛ, hmSup⟩ := Finset.exists_mem_eq_sup' hΛ d
    have hmax : ∀ b ∈ Λ, d b ≤ d m := by
      intro b hb
      calc
        d b ≤ Λ.sup' hΛ d := Finset.le_sup' d hb
        _ = d m := hmSup
    have hdm_nonneg : 0 ≤ d m := hd_nonneg m hmΛ
    by_cases hdm : d m = 0
    · intro a ha
      have hle : d a ≤ 0 := by simpa [hdm] using hmax a ha
      exact le_antisymm hle (hd_nonneg a ha)
    · have hdm_pos : 0 < d m := lt_of_le_of_ne hdm_nonneg (Ne.symm hdm)
      have hsum_le :
          Finset.sum Λ (fun b => c m b * d b) ≤
            Finset.sum Λ (fun b => c m b * d m) := by
        refine Finset.sum_le_sum ?_
        intro b hb
        exact mul_le_mul_of_nonneg_left (hmax b hb) (hc_nonneg m b)
      have hstrict :
          Finset.sum Λ (fun b => c m b * d m) < d m := by
        have hmrow : Finset.sum Λ (fun b => c m b) < 1 := hrows m hmΛ
        have hstrict' : (Finset.sum Λ (fun b => c m b)) * d m < d m := by
          nlinarith
        have h_sum_right :
            ∀ t : Finset Atom,
              Finset.sum t (fun b => c m b * d m) =
                (Finset.sum t (fun b => c m b)) * d m := by
          intro t
          induction t using Finset.induction_on with
          | empty =>
              simp
          | @insert x s hx ih =>
              simp [Finset.sum_insert, hx, ih, add_mul]
        rw [h_sum_right Λ]
        exact hstrict'
      have : d m < d m := lt_of_le_of_lt (le_trans (hd_le m hmΛ) hsum_le) hstrict
      exact (lt_irrefl _ this).elim
  · intro a ha
    exact (hΛ ⟨a, ha⟩).elim

theorem finiteRegion_eq_zero_of_nonneg_le_sum_pairwiseDobrushinCoefficient
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hd_nonneg : ∀ a ∈ Λ, 0 ≤ d a)
    (hd_le : ∀ a ∈ Λ,
      d a ≤ Finset.sum Λ (fun b => M.pairwiseDobrushinCoefficient a b * d b)) :
    ∀ a ∈ Λ, d a = 0 := by
  exact finiteRegion_eq_zero_of_nonneg_le_sum_of_rowSums_lt_one
    (hc_nonneg := fun a b => M.pairwiseDobrushinCoefficient_nonneg a b)
    (hrows := fun a ha => M.finiteRegion_pairwiseDobrushinRowSum_lt_one hM Λ a)
    (hd_nonneg := hd_nonneg)
    (hd_le := hd_le)

/-- Uniqueness target at the current honest theorem layer:
there is at most one probability measure satisfying fixed-region cylinder DLR. -/
def UniqueFixedRegionCylinderDLR
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId) : Prop :=
  ∀ (μ ν : ProbabilityMeasure (InfiniteWorld Atom)),
    FixedRegionCylinderDLR M (μ : Measure (InfiniteWorld Atom)) →
      FixedRegionCylinderDLR M (ν : Measure (InfiniteWorld Atom)) →
        (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom))

/-- Paper-style uniqueness target for the classical weighted-clause surface. -/
def PaperUniqueMeasure
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) : Prop :=
  UniqueFixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec

end ClassicalInfiniteGroundMLNSpec

end Mettapedia.Logic.PLNMarkovLogicInfiniteUniqueness
