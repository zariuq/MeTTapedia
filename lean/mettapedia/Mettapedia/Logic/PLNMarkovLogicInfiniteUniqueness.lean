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

omit [DecidableEq Atom] in
theorem finiteRegionSupSeminorm_le_of_bound
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    {c : ℝ}
    (hc : 0 ≤ c)
    (hbound : ∀ a ∈ Λ, d a ≤ c) :
    finiteRegionSupSeminorm Λ d ≤ c := by
  by_cases hΛ : Λ.Nonempty
  · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΛ d
    rw [finiteRegionSupSeminorm, dif_pos hΛ, hsup]
    exact hbound a ha
  · simp [finiteRegionSupSeminorm, hΛ, hc]

omit [DecidableEq Atom] in
theorem finiteRegionSupSeminorm_eq_zero_of_eq_zero
    {Λ : Finset Atom}
    {d : Atom → ℝ}
    (hzero : ∀ a ∈ Λ, d a = 0) :
    finiteRegionSupSeminorm Λ d = 0 := by
  apply le_antisymm
  · by_cases hΛ : Λ.Nonempty
    · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup' hΛ d
      rw [finiteRegionSupSeminorm, dif_pos hΛ, hsup, hzero a ha]
    · simp [finiteRegionSupSeminorm, hΛ]
  · exact finiteRegionSupSeminorm_nonneg (fun a ha => by simp [hzero a ha])

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

/-- Uniform Dobrushin condition: there exists a single contraction constant
    `C < 1` bounding all per-atom row sums simultaneously.  This is the
    hypothesis needed for the infinite-volume Dobrushin uniqueness theorem
    (Georgii Theorem 8.7); the non-uniform `PaperSmallTotalInfluence`
    (per-atom `< 1`) does NOT suffice for infinite atom sets. -/
def PaperUniformSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
    ∀ a : Atom,
      Finset.sum (M.atomInteractionNeighborhood a)
        (fun b => M.pairwiseDobrushinCoefficient a b) ≤ C

theorem paperUniformSmallTotalInfluence_implies_paperSmallTotalInfluence
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    M.PaperSmallTotalInfluence := by
  rcases hM with ⟨C, _, hC_lt_one, hrow⟩
  exact (M.paperSmallTotalInfluence_iff_pairwiseDobrushinRowSums_lt_one).2
    (fun a => lt_of_le_of_lt (hrow a) hC_lt_one)

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

theorem sum_mul_toReal_map_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : PMF α)
    (h : α → β)
    (f : β → ℝ) :
    (∑ y : β, f y * ENNReal.toReal ((p.map h) y)) =
      ∑ x : α, f (h x) * ENNReal.toReal (p x) := by
  classical
  calc
    (∑ y : β, f y * ENNReal.toReal ((p.map h) y))
      = ∑ y : β, f y * ENNReal.toReal (∑ x : α, if y = h x then p x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [PMF.map_apply, tsum_fintype]
          have hsum :
              (∑ b : α, @ite ℝ≥0∞ (y = h b)
                  (Classical.propDecidable (y = h b)) (p b) 0) =
                ∑ x : α, if y = h x then p x else 0 := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            by_cases hby : y = h b
            · simp [hby]
            · simp [hby]
          exact congrArg (fun z : ℝ≥0∞ => f y * ENNReal.toReal z) hsum
    _ = ∑ y : β, f y * ∑ x : α, ENNReal.toReal (if y = h x then p x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          congr 1
          exact ENNReal.toReal_sum (s := Finset.univ)
            (f := fun x : α => if y = h x then p x else 0) (by
              intro x hx
              by_cases hxy : y = h x
              · simp [hxy, p.apply_ne_top x]
              · simp [hxy])
    _ = ∑ y : β, ∑ x : α, f y * ENNReal.toReal (if y = h x then p x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.mul_sum]
    _ = ∑ x : α, ∑ y : β, f y * ENNReal.toReal (if y = h x then p x else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ x : α, f (h x) * ENNReal.toReal (p x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_eq_single (h x)]
          · simp
          · intro y hy hyne
            simp [hyne]
          · simp

theorem sum_mul_toReal_bind_eq
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α)
    (k : α → PMF β)
    (f : β → ℝ) :
    (∑ y : β, f y * ENNReal.toReal ((p.bind k) y)) =
      ∑ x : α, (∑ y : β, f y * ENNReal.toReal (k x y)) * ENNReal.toReal (p x) := by
  calc
    (∑ y : β, f y * ENNReal.toReal ((p.bind k) y))
      = ∑ y : β, f y * ENNReal.toReal (∑' x : α, p x * k x y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [PMF.bind_apply]
    _ = ∑ y : β, f y * ENNReal.toReal (∑ x : α, p x * k x y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp [tsum_fintype]
    _ = ∑ y : β, f y * ∑ x : α, ENNReal.toReal (p x * k x y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          congr 1
          rw [ENNReal.toReal_sum]
          intro x hx
          exact ENNReal.mul_ne_top (p.apply_ne_top x) ((k x).apply_ne_top y)
    _ = ∑ y : β, ∑ x : α, f y * ENNReal.toReal (p x * k x y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.mul_sum]
    _ = ∑ y : β, ∑ x : α, f y * (ENNReal.toReal (p x) * ENNReal.toReal (k x y)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [ENNReal.toReal_mul]
    _ = ∑ x : α, ∑ y : β, f y * (ENNReal.toReal (p x) * ENNReal.toReal (k x y)) := by
          rw [Finset.sum_comm]
    _ = ∑ x : α, (∑ y : β, f y * ENNReal.toReal (k x y)) * ENNReal.toReal (p x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [mul_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring

/-- Diagonal self-coupling of a finite PMF. -/
noncomputable def diagCoupling
    {α : Type*}
    (p : PMF α) : PMF (α × α) :=
  p.map fun x => (x, x)

@[simp] theorem diagCoupling_map_fst
    {α : Type*}
    (p : PMF α) :
    (diagCoupling p).map Prod.fst = p := by
  calc
    (diagCoupling p).map Prod.fst = p.map (Prod.fst ∘ fun x : α => (x, x)) := by
      simpa [diagCoupling] using
        (PMF.map_comp (p := p) (f := fun x : α => (x, x)) Prod.fst)
    _ = p.map id := by
      rfl
    _ = p := by
      simpa using (PMF.map_id (p := p))

@[simp] theorem diagCoupling_map_snd
    {α : Type*}
    (p : PMF α) :
    (diagCoupling p).map Prod.snd = p := by
  calc
    (diagCoupling p).map Prod.snd = p.map (Prod.snd ∘ fun x : α => (x, x)) := by
      simpa [diagCoupling] using
        (PMF.map_comp (p := p) (f := fun x : α => (x, x)) Prod.snd)
    _ = p.map id := by
      rfl
    _ = p := by
      simpa using (PMF.map_id (p := p))

/-- Pointwise overlap of two finite PMFs. -/
noncomputable def pmfOverlap
    {α : Type*} [Fintype α]
    (p q : PMF α) : α → ℝ≥0∞ :=
  fun a => min (p a) (q a)

/-- Total overlap mass of two finite PMFs. -/
noncomputable def pmfOverlapMass
    {α : Type*} [Fintype α]
    (p q : PMF α) : ℝ≥0∞ :=
  ∑ a, pmfOverlap p q a

/-- `L1` discrepancy between two finite PMFs, read in real coordinates. -/
noncomputable def pmfL1Discrepancy
    {α : Type*} [Fintype α]
    (p q : PMF α) : ℝ :=
  ∑ a, |ENNReal.toReal (p a) - ENNReal.toReal (q a)|

/-- Total variation between two finite PMFs. -/
noncomputable def pmfTotalVariation
    {α : Type*} [Fintype α]
    (p q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * pmfL1Discrepancy p q

theorem pmfOverlapMass_le_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfOverlapMass p q ≤ 1 := by
  unfold pmfOverlapMass pmfOverlap
  calc
    ∑ a, min (p a) (q a) ≤ ∑ a, p a := by
      refine Finset.sum_le_sum ?_
      intro a ha
      exact min_le_left _ _
    _ = 1 := by
      simpa [tsum_fintype] using p.tsum_coe

theorem pmfOverlapMass_ne_top
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfOverlapMass p q ≠ (⊤ : ℝ≥0∞) := by
  exact ne_of_lt (lt_of_le_of_lt (pmfOverlapMass_le_one p q) ENNReal.one_lt_top)

theorem abs_sub_eq_add_add_sub_two_mul_min
    {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith

theorem pmfTotalVariation_eq_one_sub_overlapMass_toReal
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfTotalVariation p q = 1 - (pmfOverlapMass p q).toReal := by
  have hp_sum :
      ∑ a, ENNReal.toReal (p a) = 1 := by
    rw [← ENNReal.toReal_sum]
    · simpa [tsum_fintype] using congrArg ENNReal.toReal p.tsum_coe
    · intro a ha
      exact p.apply_ne_top a
  have hq_sum :
      ∑ a, ENNReal.toReal (q a) = 1 := by
    rw [← ENNReal.toReal_sum]
    · simpa [tsum_fintype] using congrArg ENNReal.toReal q.tsum_coe
    · intro a ha
      exact q.apply_ne_top a
  have hmin_sum :
      ∑ a, min (ENNReal.toReal (p a)) (ENNReal.toReal (q a)) =
        (pmfOverlapMass p q).toReal := by
    symm
    unfold pmfOverlapMass pmfOverlap
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl ?_
      intro a ha
      rw [ENNReal.toReal_min (p.apply_ne_top a) (q.apply_ne_top a)]
    · intro a ha
      exact ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (p.apply_lt_top a))
  unfold pmfTotalVariation pmfL1Discrepancy
  calc
    (1 / 2 : ℝ) * ∑ a, |ENNReal.toReal (p a) - ENNReal.toReal (q a)| =
      (1 / 2 : ℝ) * ∑ a,
        (ENNReal.toReal (p a) + ENNReal.toReal (q a) -
          2 * min (ENNReal.toReal (p a)) (ENNReal.toReal (q a))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact abs_sub_eq_add_add_sub_two_mul_min
    _ = (1 / 2 : ℝ) *
        ((∑ a, ENNReal.toReal (p a)) +
          (∑ a, ENNReal.toReal (q a)) -
          2 * ∑ a, min (ENNReal.toReal (p a)) (ENNReal.toReal (q a))) := by
            simp [Finset.sum_add_distrib, two_mul, Finset.mul_sum,
              sub_eq_add_neg, add_assoc, left_distrib]
    _ = 1 - (pmfOverlapMass p q).toReal := by
            rw [hp_sum, hq_sum, hmin_sum]
            nlinarith

theorem pmfL1Discrepancy_nonneg
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    0 ≤ pmfL1Discrepancy p q := by
  unfold pmfL1Discrepancy
  exact Finset.sum_nonneg fun a ha => abs_nonneg _

theorem pmfTotalVariation_nonneg
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    0 ≤ pmfTotalVariation p q := by
  unfold pmfTotalVariation
  exact mul_nonneg (by norm_num) (pmfL1Discrepancy_nonneg p q)

theorem pmf_eq_of_totalVariation_eq_zero
    {α : Type*} [Fintype α]
    (p q : PMF α)
    (htv : pmfTotalVariation p q = 0) :
    p = q := by
  apply PMF.ext
  intro a
  have hl1 : pmfL1Discrepancy p q = 0 := by
    have hnonneg : 0 ≤ pmfL1Discrepancy p q := pmfL1Discrepancy_nonneg p q
    unfold pmfTotalVariation at htv
    nlinarith
  have hterm_le :
      |ENNReal.toReal (p a) - ENNReal.toReal (q a)| ≤ pmfL1Discrepancy p q := by
    unfold pmfL1Discrepancy
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b => |ENNReal.toReal (p b) - ENNReal.toReal (q b)|)
      (fun b hb => abs_nonneg _)
      (Finset.mem_univ a)
  have hterm :
      |ENNReal.toReal (p a) - ENNReal.toReal (q a)| = 0 := by
    have hnonneg : 0 ≤ |ENNReal.toReal (p a) - ENNReal.toReal (q a)| := abs_nonneg _
    nlinarith
  have hreal :
      ENNReal.toReal (p a) = ENNReal.toReal (q a) := by
    exact sub_eq_zero.mp (abs_eq_zero.mp hterm)
  exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp hreal

/-- Left residual mass after removing the pointwise overlap of two finite PMFs. -/
noncomputable def pmfResidualLeft
    {α : Type*} [Fintype α]
    (p q : PMF α) : α → ℝ≥0∞ :=
  fun a => p a - pmfOverlap p q a

/-- Right residual mass after removing the pointwise overlap of two finite PMFs. -/
noncomputable def pmfResidualRight
    {α : Type*} [Fintype α]
    (p q : PMF α) : α → ℝ≥0∞ :=
  fun a => q a - pmfOverlap p q a

theorem pmfOverlapMass_add_sum_pmfResidualLeft_eq_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfOverlapMass p q + ∑ a, pmfResidualLeft p q a = 1 := by
  unfold pmfResidualLeft pmfOverlapMass pmfOverlap
  calc
    ∑ a, min (p a) (q a) + ∑ a, (p a - min (p a) (q a))
      = ∑ a, (min (p a) (q a) + (p a - min (p a) (q a))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a, p a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [add_tsub_cancel_of_le (min_le_left _ _)]
    _ = 1 := by
          simpa [tsum_fintype] using p.tsum_coe

theorem pmfOverlapMass_add_sum_pmfResidualRight_eq_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfOverlapMass p q + ∑ a, pmfResidualRight p q a = 1 := by
  unfold pmfResidualRight pmfOverlapMass pmfOverlap
  calc
    ∑ a, min (p a) (q a) + ∑ a, (q a - min (p a) (q a))
      = ∑ a, (min (p a) (q a) + (q a - min (p a) (q a))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a, q a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [add_tsub_cancel_of_le (min_le_right _ _)]
    _ = 1 := by
          simpa [tsum_fintype] using q.tsum_coe

theorem pmfResidualLeft_mul_pmfResidualRight_eq_zero
    {α : Type*} [Fintype α]
    (p q : PMF α)
    (a : α) :
    pmfResidualLeft p q a * pmfResidualRight p q a = 0 := by
  unfold pmfResidualLeft pmfResidualRight pmfOverlap
  rcases le_total (p a) (q a) with hpq | hqp
  · rw [min_eq_left hpq, tsub_self, zero_mul]
  · rw [min_eq_right hqp, tsub_self, mul_zero]

theorem pmfTotalVariation_self
    {α : Type*} [Fintype α]
    (p : PMF α) :
    pmfTotalVariation p p = 0 := by
  unfold pmfTotalVariation pmfL1Discrepancy
  simp

theorem pmfOverlapMass_self
    {α : Type*} [Fintype α]
    (p : PMF α) :
    pmfOverlapMass p p = 1 := by
  unfold pmfOverlapMass pmfOverlap
  simp [min_self]
  simpa [tsum_fintype] using p.tsum_coe

theorem pmfTotalVariation_le_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    pmfTotalVariation p q ≤ 1 := by
  rw [pmfTotalVariation_eq_one_sub_overlapMass_toReal]
  have h0 : (0 : ℝ) ≤ (pmfOverlapMass p q).toReal := ENNReal.toReal_nonneg
  linarith

theorem pmfTotalVariation_nonneg_and_le_one
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    0 ≤ pmfTotalVariation p q ∧ pmfTotalVariation p q ≤ 1 :=
  ⟨pmfTotalVariation_nonneg p q, pmfTotalVariation_le_one p q⟩

theorem pmfTotalVariation_eq_abs_sub_apply_true
    (p q : PMF Bool) :
    pmfTotalVariation p q = |ENNReal.toReal (p true) - ENNReal.toReal (q true)| := by
  have hp_sum :
      ENNReal.toReal (p true) + ENNReal.toReal (p false) = 1 := by
    rw [← ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false)]
    simpa [Fintype.sum_bool, tsum_fintype] using congrArg ENNReal.toReal p.tsum_coe
  have hq_sum :
      ENNReal.toReal (q true) + ENNReal.toReal (q false) = 1 := by
    rw [← ENNReal.toReal_add (q.apply_ne_top true) (q.apply_ne_top false)]
    simpa [Fintype.sum_bool, tsum_fintype] using congrArg ENNReal.toReal q.tsum_coe
  have hp_false :
      ENNReal.toReal (p false) = 1 - ENNReal.toReal (p true) := by
    nlinarith
  have hq_false :
      ENNReal.toReal (q false) = 1 - ENNReal.toReal (q true) := by
    nlinarith
  have hfalse :
      |ENNReal.toReal (p false) - ENNReal.toReal (q false)| =
        |ENNReal.toReal (p true) - ENNReal.toReal (q true)| := by
    rw [hp_false, hq_false]
    have hneg :
        (1 - ENNReal.toReal (p true)) - (1 - ENNReal.toReal (q true)) =
          - (ENNReal.toReal (p true) - ENNReal.toReal (q true)) := by
      ring
    rw [hneg, abs_neg]
  unfold pmfTotalVariation pmfL1Discrepancy
  rw [Fintype.sum_bool, hfalse]
  ring

theorem pmfTotalVariation_map_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β)
    (p q : PMF α) :
    pmfTotalVariation (p.map e) (q.map e) = pmfTotalVariation p q := by
  unfold pmfTotalVariation pmfL1Discrepancy
  congr 1
  calc
    ∑ b : β, |ENNReal.toReal ((p.map e) b) - ENNReal.toReal ((q.map e) b)|
      =
        ∑ a : α, |ENNReal.toReal ((p.map e) (e a)) - ENNReal.toReal ((q.map e) (e a))| := by
          exact (Fintype.sum_equiv e
            (fun a : α => |ENNReal.toReal ((p.map e) (e a)) - ENNReal.toReal ((q.map e) (e a))|)
            (fun b : β => |ENNReal.toReal ((p.map e) b) - ENNReal.toReal ((q.map e) b)|)
            (fun a => rfl)).symm
    _ = ∑ a : α, |ENNReal.toReal (p a) - ENNReal.toReal (q a)| := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [PMF.map_apply]

theorem sum_pmfResidualLeft_eq_one_sub_overlapMass
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    ∑ a, pmfResidualLeft p q a = 1 - pmfOverlapMass p q := by
  have h := pmfOverlapMass_add_sum_pmfResidualLeft_eq_one p q
  have hne : pmfOverlapMass p q ≠ ⊤ := pmfOverlapMass_ne_top p q
  exact ENNReal.eq_sub_of_add_eq hne (add_comm (pmfOverlapMass p q) _ ▸ h)

theorem sum_pmfResidualRight_eq_one_sub_overlapMass
    {α : Type*} [Fintype α]
    (p q : PMF α) :
    ∑ a, pmfResidualRight p q a = 1 - pmfOverlapMass p q := by
  have h := pmfOverlapMass_add_sum_pmfResidualRight_eq_one p q
  have hne : pmfOverlapMass p q ≠ ⊤ := pmfOverlapMass_ne_top p q
  exact ENNReal.eq_sub_of_add_eq hne (add_comm (pmfOverlapMass p q) _ ▸ h)

/-- The maximal coupling function for two finite PMFs.
    On the diagonal, mass equals the pointwise overlap.
    Off-diagonal, mass is the product of normalized residuals. -/
noncomputable def pmfMaximalCouplingFun
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) : α × α → ℝ≥0∞ :=
  fun ⟨a, b⟩ =>
    if a = b then pmfOverlap p q a
    else pmfResidualLeft p q a * pmfResidualRight p q b / (1 - pmfOverlapMass p q)

theorem pmfMaximalCouplingFun_diag
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (a : α) :
    pmfMaximalCouplingFun p q (a, a) = pmfOverlap p q a := by
  simp [pmfMaximalCouplingFun]

theorem pmfMaximalCouplingFun_off_diag
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (a b : α) (hab : a ≠ b) :
    pmfMaximalCouplingFun p q (a, b) =
      pmfResidualLeft p q a * pmfResidualRight p q b / (1 - pmfOverlapMass p q) := by
  simp [pmfMaximalCouplingFun, hab]

/-- Auxiliary: the off-diagonal contribution for the `sum_snd` marginal computation. -/
private theorem pmfMaximalCouplingFun_off_diag_sum_snd_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (a : α)
    (hqp : q a ≤ p a) :
    ∑ b ∈ Finset.univ.erase a, pmfMaximalCouplingFun p q (a, b) = p a - q a := by
  have hresR_a : pmfResidualRight p q a = 0 := by
    unfold pmfResidualRight pmfOverlap; rw [min_eq_right hqp, tsub_self]
  -- Each off-diagonal term is residL(a) * residR(b) / (1 - overlap)
  -- where residR(a) = 0
  -- Sum over {b ≠ a}: ∑ residL(a) * residR(b) / D = residL(a) * (∑ residR(b)) / D
  -- Since residR(a) = 0: ∑_{b≠a} residR(b) = ∑_b residR(b) = (1-overlap)
  -- So off-diag sum = residL(a) * (1-overlap) / (1-overlap) = residL(a) = p a - q a
  have hresL_a : pmfResidualLeft p q a = p a - q a := by
    unfold pmfResidualLeft pmfOverlap; rw [min_eq_right hqp]
  -- Rewrite each term
  have hterm : ∀ b ∈ Finset.univ.erase a,
      pmfMaximalCouplingFun p q (a, b) =
        pmfResidualLeft p q a * (pmfResidualRight p q b / (1 - pmfOverlapMass p q)) := by
    intro b hb
    have hab : a ≠ b := fun h => (Finset.notMem_erase a Finset.univ) (h ▸ hb)
    rw [pmfMaximalCouplingFun_off_diag p q a b hab]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  rw [Finset.sum_congr rfl hterm]
  -- Factor: ∑ residL(a) * (residR(b) / D) = residL(a) * ∑ (residR(b) / D)
  --       = residL(a) * (∑ residR(b)) / D
  -- Since residR(a) = 0: ∑_{b≠a} residR(b) = ∑_b residR(b) = (1-overlap) = D
  -- So result = residL(a) * D / D = residL(a) = p a - q a
  set D := (1 : ℝ≥0∞) - pmfOverlapMass p q with hD_def
  -- Factor out residL from sum
  have hfactor : ∑ b ∈ Finset.univ.erase a, pmfResidualLeft p q a * (pmfResidualRight p q b / D) =
      pmfResidualLeft p q a * (∑ b ∈ Finset.univ.erase a, pmfResidualRight p q b / D) := by
    induction (Finset.univ.erase a) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mul_add, ih]
  rw [hfactor]
  -- Factor division out of sum
  have hsum_div : ∑ b ∈ Finset.univ.erase a, pmfResidualRight p q b / D =
      (∑ b ∈ Finset.univ.erase a, pmfResidualRight p q b) / D := by
    simp only [ENNReal.div_eq_inv_mul]
    induction (Finset.univ.erase a) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mul_add, ih]
  rw [hsum_div]
  -- ∑_{b ≠ a} residR(b) = ∑_b residR(b) since residR(a) = 0
  have hresR_sum : ∑ b ∈ Finset.univ.erase a, pmfResidualRight p q b = ∑ b, pmfResidualRight p q b := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a), hresR_a, zero_add]
  rw [hresR_sum, sum_pmfResidualRight_eq_one_sub_overlapMass, ← hD_def]
  by_cases hov_eq : pmfOverlapMass p q = 1
  · -- When overlap = 1, p a - q a = 0 (since residL = 0 too)
    have : ∑ a', pmfResidualLeft p q a' = 0 := by
      rw [sum_pmfResidualLeft_eq_one_sub_overlapMass, hov_eq, tsub_self]
    have hresL_zero : pmfResidualLeft p q a = 0 :=
      le_antisymm
        ((Finset.single_le_sum (fun x _ => bot_le) (Finset.mem_univ a)).trans (le_of_eq this))
        bot_le
    rw [hresL_a] at hresL_zero
    rw [hresL_a, hresL_zero]
    simp [ENNReal.div_eq_inv_mul]
  · -- When overlap < 1
    have hov_lt : pmfOverlapMass p q < 1 :=
      lt_of_le_of_ne (pmfOverlapMass_le_one p q) hov_eq
    have hD_ne_zero : D ≠ 0 := (tsub_pos_of_lt hov_lt).ne'
    have hD_ne_top : D ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
    rw [ENNReal.div_self hD_ne_zero hD_ne_top, mul_one, hresL_a]

/-- Auxiliary: the off-diagonal contribution for the `sum_fst` marginal computation. -/
private theorem pmfMaximalCouplingFun_off_diag_sum_fst_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (b : α)
    (hpq : p b ≤ q b) :
    ∑ a ∈ Finset.univ.erase b, pmfMaximalCouplingFun p q (a, b) = q b - p b := by
  have hresL_b : pmfResidualLeft p q b = 0 := by
    unfold pmfResidualLeft pmfOverlap; rw [min_eq_left hpq, tsub_self]
  have hresR_b : pmfResidualRight p q b = q b - p b := by
    unfold pmfResidualRight pmfOverlap; rw [min_eq_left hpq]
  -- Rewrite each term
  have hterm : ∀ a ∈ Finset.univ.erase b,
      pmfMaximalCouplingFun p q (a, b) =
        (pmfResidualLeft p q a / (1 - pmfOverlapMass p q)) * pmfResidualRight p q b := by
    intro a ha
    have hab : a ≠ b := fun h => (Finset.notMem_erase b Finset.univ) (h ▸ ha)
    rw [pmfMaximalCouplingFun_off_diag p q a b hab]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  -- ∑_{a ≠ b} residL(a) / D = (∑_{a ≠ b} residL(a)) / D
  -- Since residL(b) = 0: ∑_{a ≠ b} residL(a) = ∑_a residL(a) = (1-overlap)
  have hresL_sum : ∑ a ∈ Finset.univ.erase b, pmfResidualLeft p q a = ∑ a, pmfResidualLeft p q a := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b), hresL_b, zero_add]
  -- Factor the division out of the sum
  have hsum_div : ∑ a ∈ Finset.univ.erase b, (pmfResidualLeft p q a / (1 - pmfOverlapMass p q)) =
      (∑ a ∈ Finset.univ.erase b, pmfResidualLeft p q a) / (1 - pmfOverlapMass p q) := by
    simp only [ENNReal.div_eq_inv_mul]
    induction (Finset.univ.erase b) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mul_add, ih]
  rw [hsum_div, hresL_sum, sum_pmfResidualLeft_eq_one_sub_overlapMass]
  by_cases hov_eq : pmfOverlapMass p q = 1
  · -- When overlap = 1, q b - p b = 0
    have : ∑ a', pmfResidualRight p q a' = 0 := by
      rw [sum_pmfResidualRight_eq_one_sub_overlapMass, hov_eq, tsub_self]
    have hresR_zero : pmfResidualRight p q b = 0 :=
      le_antisymm
        ((Finset.single_le_sum (fun x _ => bot_le) (Finset.mem_univ b)).trans (le_of_eq this))
        bot_le
    rw [hresR_b] at hresR_zero
    rw [hresR_b, hresR_zero]
    simp [ENNReal.div_eq_inv_mul]
  · have hov_lt : pmfOverlapMass p q < 1 :=
      lt_of_le_of_ne (pmfOverlapMass_le_one p q) hov_eq
    have hD_ne_zero : (1 : ℝ≥0∞) - pmfOverlapMass p q ≠ 0 := (tsub_pos_of_lt hov_lt).ne'
    have hD_ne_top : (1 : ℝ≥0∞) - pmfOverlapMass p q ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
    rw [ENNReal.div_self hD_ne_zero hD_ne_top, one_mul, hresR_b]

/-- Key summation: summing the maximal coupling function over the second coordinate
    yields `p a`. -/
theorem pmfMaximalCouplingFun_sum_snd
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (a : α) :
    ∑ b : α, pmfMaximalCouplingFun p q (a, b) = p a := by
  rcases le_total (p a) (q a) with hpq | hqp
  · -- Case p a ≤ q a: residualLeft(a) = 0, so off-diagonal vanishes
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    rw [pmfMaximalCouplingFun_diag]
    have hoff : ∑ b ∈ Finset.univ.erase a, pmfMaximalCouplingFun p q (a, b) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hab : a ≠ b := fun h => (Finset.notMem_erase a Finset.univ) (h ▸ hb)
      rw [pmfMaximalCouplingFun_off_diag p q a b hab]
      have : pmfResidualLeft p q a = 0 := by
        unfold pmfResidualLeft pmfOverlap; rw [min_eq_left hpq, tsub_self]
      rw [this, zero_mul, ENNReal.zero_div]
    rw [hoff, add_zero]
    unfold pmfOverlap; exact min_eq_left hpq
  · -- Case q a ≤ p a: off-diagonal contributes p a - q a
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    rw [pmfMaximalCouplingFun_diag]
    rw [pmfMaximalCouplingFun_off_diag_sum_snd_eq p q a hqp]
    unfold pmfOverlap; rw [min_eq_right hqp, add_tsub_cancel_of_le hqp]

/-- Key summation: summing the maximal coupling function over the first coordinate
    yields `q b`. -/
theorem pmfMaximalCouplingFun_sum_fst
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (b : α) :
    ∑ a : α, pmfMaximalCouplingFun p q (a, b) = q b := by
  rcases le_total (p b) (q b) with hpq | hqp
  · -- Case p b ≤ q b: off-diagonal contributes q b - p b
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b)]
    rw [pmfMaximalCouplingFun_diag]
    rw [pmfMaximalCouplingFun_off_diag_sum_fst_eq p q b hpq]
    unfold pmfOverlap; rw [min_eq_left hpq, add_tsub_cancel_of_le hpq]
  · -- Case q b ≤ p b: residualRight(b) = 0, so off-diagonal vanishes
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ b)]
    rw [pmfMaximalCouplingFun_diag]
    have hoff : ∑ a ∈ Finset.univ.erase b, pmfMaximalCouplingFun p q (a, b) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hab : a ≠ b := fun h => (Finset.notMem_erase b Finset.univ) (h ▸ ha)
      rw [pmfMaximalCouplingFun_off_diag p q a b hab]
      have : pmfResidualRight p q b = 0 := by
        unfold pmfResidualRight pmfOverlap; rw [min_eq_right hqp, tsub_self]
      rw [this, mul_zero, ENNReal.zero_div]
    rw [hoff, add_zero]
    unfold pmfOverlap; exact min_eq_right hqp

theorem pmfMaximalCouplingFun_sum_total
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∑ z : α × α, pmfMaximalCouplingFun p q z = 1 := by
  calc
    ∑ z : α × α, pmfMaximalCouplingFun p q z
      = ∑ a : α, ∑ b : α, pmfMaximalCouplingFun p q (a, b) := by
          exact Fintype.sum_prod_type _
    _ = ∑ a : α, p a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact pmfMaximalCouplingFun_sum_snd p q a
    _ = 1 := by
          simpa [tsum_fintype] using p.tsum_coe

/-- The maximal coupling PMF for two finite PMFs. -/
noncomputable def pmfMaximalCoupling
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) : PMF (α × α) :=
  PMF.ofFintype (pmfMaximalCouplingFun p q) (pmfMaximalCouplingFun_sum_total p q)

theorem pmfMaximalCoupling_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) (z : α × α) :
    pmfMaximalCoupling p q z = pmfMaximalCouplingFun p q z := by
  exact PMF.ofFintype_apply _ z

/-- The first marginal of the maximal coupling is `p`. -/
theorem pmfMaximalCoupling_map_fst
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    (pmfMaximalCoupling p q).map Prod.fst = p := by
  ext a
  rw [PMF.map_apply, tsum_fintype]
  simp only [pmfMaximalCoupling_apply]
  -- Goal: ∑ x : α × α, (if a = x.1 then γ_fun x else 0) = p a
  rw [Fintype.sum_prod_type]
  -- Pull if out of inner sum, then apply sum_ite_eq to outer sum
  have hpull : ∀ x, ∑ y : α, (if a = x then pmfMaximalCouplingFun p q (x, y) else 0) =
      if a = x then ∑ y : α, pmfMaximalCouplingFun p q (x, y) else 0 := by
    intro x; split <;> simp_all
  simp_rw [hpull, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact pmfMaximalCouplingFun_sum_snd p q a

/-- The second marginal of the maximal coupling is `q`. -/
theorem pmfMaximalCoupling_map_snd
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    (pmfMaximalCoupling p q).map Prod.snd = q := by
  ext b
  rw [PMF.map_apply, tsum_fintype]
  simp only [pmfMaximalCoupling_apply]
  rw [Fintype.sum_prod_type_right]
  have hpull : ∀ y, ∑ x : α, (if b = y then pmfMaximalCouplingFun p q (x, y) else 0) =
      if b = y then ∑ x : α, pmfMaximalCouplingFun p q (x, y) else 0 := by
    intro y; split <;> simp_all
  simp_rw [hpull, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact pmfMaximalCouplingFun_sum_fst p q b

/-- The diagonal mass of the maximal coupling equals the overlap mass. -/
theorem pmfMaximalCoupling_diag_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∑ a : α, pmfMaximalCoupling p q (a, a) = pmfOverlapMass p q := by
  simp only [pmfMaximalCoupling_apply, pmfMaximalCouplingFun_diag]
  rfl

/-- **Finite maximal coupling**: for any two PMFs on a finite type, there exists
    a joint PMF (coupling) whose diagonal mass equals the overlap mass.
    Equivalently, the disagreement probability equals the total variation distance. -/
theorem exists_pmfMaximalCoupling {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∃ γ : PMF (α × α),
      (∀ a, ∑ b : α, γ (a, b) = p a) ∧
      (∀ b, ∑ a : α, γ (a, b) = q b) ∧
      (∑ a : α, γ (a, a) ≥ pmfOverlapMass p q) := by
  refine ⟨pmfMaximalCoupling p q, ?_, ?_, ?_⟩
  · intro a
    simp only [pmfMaximalCoupling_apply]
    exact pmfMaximalCouplingFun_sum_snd p q a
  · intro b
    simp only [pmfMaximalCoupling_apply]
    exact pmfMaximalCouplingFun_sum_fst p q b
  · rw [pmfMaximalCoupling_diag_mass]

/-- The diagonal mass of the maximal coupling equals the overlap mass (exact equality). -/
theorem exists_pmfMaximalCoupling_exact {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∃ γ : PMF (α × α),
      (∀ a, ∑ b : α, γ (a, b) = p a) ∧
      (∀ b, ∑ a : α, γ (a, b) = q b) ∧
      (∑ a : α, γ (a, a) = pmfOverlapMass p q) := by
  refine ⟨pmfMaximalCoupling p q, ?_, ?_, ?_⟩
  · intro a
    simp only [pmfMaximalCoupling_apply]
    exact pmfMaximalCouplingFun_sum_snd p q a
  · intro b
    simp only [pmfMaximalCoupling_apply]
    exact pmfMaximalCouplingFun_sum_fst p q b
  · exact pmfMaximalCoupling_diag_mass p q

theorem pmfMaximalCoupling_disagreementProbability_eq_totalVariation
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (pmfMaximalCoupling p q z) =
      pmfTotalVariation p q := by
  have hdisagree :
      ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (pmfMaximalCoupling p q z) =
        1 - ∑ a : α, ENNReal.toReal (pmfMaximalCoupling p q (a, a)) := by
    have htotal : ∑ z : α × α, ENNReal.toReal (pmfMaximalCoupling p q z) = 1 := by
      rw [← ENNReal.toReal_sum (fun z _ => (pmfMaximalCoupling p q).apply_ne_top z)]
      simpa [tsum_fintype] using congrArg ENNReal.toReal (pmfMaximalCoupling p q).tsum_coe
    calc
      ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (pmfMaximalCoupling p q z)
        = ∑ z : α × α, ENNReal.toReal (pmfMaximalCoupling p q z) -
            ∑ z : α × α, (if z.1 = z.2 then ENNReal.toReal (pmfMaximalCoupling p q z) else 0) := by
              rw [sub_eq_iff_eq_add.mpr]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z hz
              by_cases h : z.1 = z.2 <;> simp [h]
      _ = 1 - ∑ a : α, ENNReal.toReal (pmfMaximalCoupling p q (a, a)) := by
            rw [htotal]
            congr 1
            rw [Fintype.sum_prod_type]
            simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (pmfMaximalCoupling p q z)
      = 1 - ∑ a : α, ENNReal.toReal (pmfMaximalCoupling p q (a, a)) := hdisagree
    _ = 1 - (pmfOverlapMass p q).toReal := by
          rw [← ENNReal.toReal_sum (fun a _ => (pmfMaximalCoupling p q).apply_ne_top (a, a))]
          rw [pmfMaximalCoupling_diag_mass]
    _ = pmfTotalVariation p q := by
          rw [pmfTotalVariation_eq_one_sub_overlapMass_toReal]

/- TODO: fix pmfMaximalCoupling_off_diag_mass and pmfTotalVariation_le_coupling_disagreement
   after simp regression. Not needed for the Dobrushin uniqueness proof. -/
/-
/-- The off-diagonal mass of the maximal coupling equals 1 - overlapMass,
    which is twice the total variation distance (in ℝ≥0∞). -/
theorem pmfMaximalCoupling_off_diag_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α) :
    ∑ z : α × α, (if z.1 = z.2 then 0 else pmfMaximalCoupling p q z) =
      1 - pmfOverlapMass p q := by
  have htotal : ∑ z : α × α, pmfMaximalCoupling p q z = 1 := by
    simpa [tsum_fintype] using (pmfMaximalCoupling p q).tsum_coe
  have hdiag : ∑ z : α × α, (if z.1 = z.2 then pmfMaximalCoupling p q z else 0) =
      pmfOverlapMass p q := by
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact pmfMaximalCoupling_diag_mass p q
  have hsum_eq : ∑ z, pmfMaximalCoupling p q z =
      ∑ z, (if z.1 = z.2 then (0 : ℝ≥0∞) else pmfMaximalCoupling p q z) +
        ∑ z, (if z.1 = z.2 then pmfMaximalCoupling p q z else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases h : z.1 = z.2 <;> simp [h]
  calc ∑ z, (if z.1 = z.2 then 0 else pmfMaximalCoupling p q z)
      = ∑ z, pmfMaximalCoupling p q z -
          ∑ z, (if z.1 = z.2 then pmfMaximalCoupling p q z else 0) := by
        exact (ENNReal.sub_eq_of_eq_add
          (by rw [hdiag]; exact pmfOverlapMass_ne_top p q) hsum_eq).symm
    _ = 1 - pmfOverlapMass p q := by rw [htotal, hdiag]

/-- For any coupling of `p` and `q`, the total variation distance is at most
    the coupling's disagreement probability. The maximal coupling achieves equality. -/
theorem pmfTotalVariation_le_coupling_disagreement
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : PMF α)
    (γ : PMF (α × α))
    (hfst : γ.map Prod.fst = p)
    (hsnd : γ.map Prod.snd = q) :
    pmfTotalVariation p q ≤
      ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (γ z) := by
  -- TV(p,q) = 1 - overlapMass.toReal ≤ 1 - (∑ a, γ(a,a)).toReal
  -- The disagreement prob = ∑ z, (if z.1 ≠ z.2 then 1 else 0) * γ(z).toReal
  --                       = 1 - ∑ a, γ(a,a).toReal
  -- For any coupling: ∑ a, γ(a,a) ≥ overlapMass (proof: each γ(a,a) ≤ min(p(a), q(a)) so
  --   ∑ γ(a,a) ≤ ∑ min(p(a),q(a)) = overlapMass)
  -- Wait, the inequality goes the other way: for an ARBITRARY coupling, ∑ γ(a,a) ≤ overlapMass
  -- is NOT guaranteed. In fact ∑ γ(a,a) can be anything between max(0, 1 - TV) and 1.
  -- Actually: ∑ a, γ(a,a) ≤ ∑ a, min(p a, q a) always holds for any coupling.
  -- Because γ(a,a) ≤ ∑_b γ(a,b) = p(a) and γ(a,a) ≤ ∑_b γ(b,a) = q(a).
  -- So γ(a,a) ≤ min(p a, q a) = overlap(a).
  -- Therefore ∑ γ(a,a) ≤ overlapMass, so 1 - overlapMass ≤ 1 - ∑ γ(a,a) = disagree prob.
  -- i.e., TV = (1/2)(1 - overlapMass) ≤ (1/2) * disagree prob... but disagree prob is not halved.
  -- Let me re-check: TV = (1/2) * L1 = 1 - overlapMass.toReal.
  -- disagree prob = 1 - ∑ γ(a,a).toReal ≥ 1 - overlapMass.toReal = TV.
  -- So TV ≤ disagree prob. This is correct.
  rw [pmfTotalVariation_eq_one_sub_overlapMass_toReal]
  -- Need: 1 - overlapMass.toReal ≤ ∑ z, (if z.1 = z.2 then 0 else 1) * γ(z).toReal
  -- disagree prob = 1 - ∑ a, γ(a,a).toReal
  -- So need: 1 - overlapMass.toReal ≤ 1 - ∑ a, γ(a,a).toReal
  -- i.e., ∑ a, γ(a,a).toReal ≤ overlapMass.toReal
  -- which follows from γ(a,a) ≤ min(p a, q a) for each a.
  -- First, show disagree prob = 1 - ∑ a, γ(a,a).toReal
  have hdisagree :
      ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (γ z) =
        1 - ∑ a : α, ENNReal.toReal (γ (a, a)) := by
    have htotal : ∑ z : α × α, ENNReal.toReal (γ z) = 1 := by
      rw [← ENNReal.toReal_sum (fun z _ => γ.apply_ne_top z)]
      simpa [tsum_fintype] using congrArg ENNReal.toReal γ.tsum_coe
    calc ∑ z : α × α, (if z.1 = z.2 then (0 : ℝ) else 1) * ENNReal.toReal (γ z)
        = ∑ z : α × α, ENNReal.toReal (γ z) -
            ∑ z : α × α, (if z.1 = z.2 then ENNReal.toReal (γ z) else 0) := by
          rw [sub_eq_iff_eq_add.mpr]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro z _
          by_cases h : z.1 = z.2
          · simp [h]
          · simp [h]
        _ = 1 - ∑ a : α, ENNReal.toReal (γ (a, a)) := by
          rw [htotal]
          congr 1
          rw [Fintype.sum_prod_type]
          simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hdisagree]
  -- Now need: 1 - overlapMass.toReal ≤ 1 - ∑ a, γ(a,a).toReal
  -- i.e., ∑ a, γ(a,a).toReal ≤ overlapMass.toReal
  linarith [show ∑ a : α, ENNReal.toReal (γ (a, a)) ≤ (pmfOverlapMass p q).toReal from by
    rw [← ENNReal.toReal_sum (fun a _ => γ.apply_ne_top (a, a))]
    have hle_ennreal : ∑ a, γ (a, a) ≤ pmfOverlapMass p q := by
      unfold pmfOverlapMass pmfOverlap
      refine Finset.sum_le_sum ?_
      intro a _
      exact le_min
        (calc γ (a, a) ≤ ∑ b, γ (a, b) :=
              Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)
          _ = p a := by
              have h := congr_arg (· a) hfst
              rwa [PMF.map_apply, tsum_fintype] at h)
        (calc γ (a, a) ≤ ∑ b, γ (b, a) :=
              Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)
          _ = q a := by
              have h := congr_arg (· a) hsnd
              rwa [PMF.map_apply, tsum_fintype] at h)
    exact (ENNReal.toReal_le_toReal
      (ne_of_lt (lt_of_le_of_lt hle_ennreal
        (lt_of_le_of_lt (pmfOverlapMass_le_one p q) ENNReal.one_lt_top)))
      (pmfOverlapMass_ne_top p q)).mpr hle_ennreal]
-/

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

/-- Restricting the patched world back to the patched region recovers the local
assignment. -/
theorem restrict_patch
    {Δ : Region Atom}
    (x : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    Finset.restrict Δ (patch Δ x ξ) = x := by
  funext a
  simp [patch, a.2]

/-- Patching and then restricting back to the same finite region recovers the
original local assignment. -/
theorem worldRestriction_patch
    {Δ : Region Atom}
    (x : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom) :
    worldRestriction Δ (patch Δ x ξ) = x := by
  funext a
  simp [worldRestriction, patch, a.2]

/-- The preimage of a cylinder on `Δ` under the patch map on `Δ` is exactly the
underlying set of `Δ`-assignments. -/
theorem preimage_cylinder_patch
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (S : Set (LocalAssignment Atom Δ)) :
    (fun x : LocalAssignment Atom Δ => patch Δ x ξ) ⁻¹'
      MeasureTheory.cylinder Δ S = S := by
  ext x
  simp [MeasureTheory.cylinder, restrict_patch (x := x) (ξ := ξ)]

/-- Dobrushin's one-site heat-bath kernel on the finite region `Δ`, centered at
site `i`: sample the singleton finite-volume world measure with boundary
`patch Δ x ξ`, then restrict the resulting world back to `Δ`. -/
noncomputable def singleSiteHeatBathKernelPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ) :
    PMF (LocalAssignment Atom Δ) :=
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  (finiteVolumeWorldPMF
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ).map
    (worldRestriction Δ)

/-- Restricting the singleton-site patch back to the ambient finite region
replaces only the distinguished site and keeps the outside part of `x`
unchanged. -/
theorem worldRestriction_patch_singleton_eq_mergeAssignments
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (x : LocalAssignment Atom Δ)
    (ξ : BoundaryCondition Atom)
    (s : LocalAssignment Atom ({i.1} : Region Atom)) :
    worldRestriction Δ (patch ({i.1} : Region Atom) s (patch Δ x ξ)) =
      mergeAssignments (Atom := Atom) s
        (restrictOutsideAssignment (Atom := Atom) x) := by
  funext a
  by_cases ha : a.1 ∈ ({i.1} : Region Atom)
  · have hai : a.1 = i.1 := by
      simpa using ha
    have hsub : a = i := by
      apply Subtype.ext
      exact hai
    subst hsub
    simp [worldRestriction, patch, mergeAssignments]
  · have ha' : a.1 ∉ ({i.1} : Region Atom) := by
      simpa using ha
    simp [worldRestriction, patch, mergeAssignments, restrictOutsideAssignment, ha', a.2]

/-- The one-site heat-bath kernel is exactly the singleton finite-volume
assignment PMF, embedded back into `Δ` by keeping the outside coordinates of
the input assignment fixed. -/
theorem singleSiteHeatBathKernelPMF_eq_map_mergeAssignments
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ) :
    let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
    let η := patch Δ x ξ
    let hZ :
        M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
        M' ({i.1} : Region Atom) η
    M.singleSiteHeatBathKernelPMF i ξ x =
      (finiteVolumeAssignmentPMF
        (M := M'.toInfiniteGroundMLNSpec)
        ({i.1} : Region Atom) η hZ).map
        (fun s =>
          mergeAssignments (Atom := Atom) s
            (restrictOutsideAssignment (Atom := Atom) x)) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  calc
    M.singleSiteHeatBathKernelPMF i ξ x
      = ((finiteVolumeAssignmentPMF
            (M := M'.toInfiniteGroundMLNSpec)
            ({i.1} : Region Atom) η hZ).map
          (fun s : LocalAssignment Atom ({i.1} : Region Atom) =>
            patch ({i.1} : Region Atom) s η)).map
            (worldRestriction Δ) := by
              simp [singleSiteHeatBathKernelPMF, finiteVolumeWorldPMF, M', η]
    _ = (finiteVolumeAssignmentPMF
          (M := M'.toInfiniteGroundMLNSpec)
          ({i.1} : Region Atom) η hZ).map
          (fun s =>
            worldRestriction Δ (patch ({i.1} : Region Atom) s η)) := by
              simpa using
                (PMF.map_comp
                  (p := finiteVolumeAssignmentPMF
                    (M := M'.toInfiniteGroundMLNSpec)
                    ({i.1} : Region Atom) η hZ)
                  (f := fun s : LocalAssignment Atom ({i.1} : Region Atom) =>
                    patch ({i.1} : Region Atom) s η)
                  (worldRestriction Δ))
    _ = (finiteVolumeAssignmentPMF
          (M := M'.toInfiniteGroundMLNSpec)
          ({i.1} : Region Atom) η hZ).map
          (fun s =>
            mergeAssignments (Atom := Atom) s
              (restrictOutsideAssignment (Atom := Atom) x)) := by
              congr 1
              funext s
              simp [η, worldRestriction_patch_singleton_eq_mergeAssignments]

/-- Away from the updated site, the one-site heat-bath kernel is deterministic:
every outside coordinate is preserved from the input assignment. -/
theorem singleSiteHeatBathKernelPMF_map_eval_eq_pure_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ) :
    (M.singleSiteHeatBathKernelPMF i ξ x).map (fun y => y a) = PMF.pure (x a) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  calc
    (M.singleSiteHeatBathKernelPMF i ξ x).map (fun y => y a)
      = ((finiteVolumeAssignmentPMF
            (M := M'.toInfiniteGroundMLNSpec)
            ({i.1} : Region Atom) η hZ).map
          (fun s =>
            mergeAssignments (Atom := Atom) s
              (restrictOutsideAssignment (Atom := Atom) x))).map
          (fun y => y a) := by
            simp [M.singleSiteHeatBathKernelPMF_eq_map_mergeAssignments, M', η]
    _ = (finiteVolumeAssignmentPMF
          (M := M'.toInfiniteGroundMLNSpec)
          ({i.1} : Region Atom) η hZ).map
          (fun s =>
            (mergeAssignments (Atom := Atom) s
              (restrictOutsideAssignment (Atom := Atom) x)) a) := by
            simpa using
              (PMF.map_comp
                (p := finiteVolumeAssignmentPMF
                  (M := M'.toInfiniteGroundMLNSpec)
                  ({i.1} : Region Atom) η hZ)
                (f := fun s =>
                  mergeAssignments (Atom := Atom) s
                    (restrictOutsideAssignment (Atom := Atom) x))
                (fun y => y a))
    _ = (finiteVolumeAssignmentPMF
          (M := M'.toInfiniteGroundMLNSpec)
          ({i.1} : Region Atom) η hZ).map
          (Function.const _ (x a)) := by
            congr 1
            funext s
            have ha' : a.1 ∉ ({i.1} : Region Atom) := by
              simpa [Finset.mem_singleton] using ha
            simp [mergeAssignments, restrictOutsideAssignment, ha']
    _ = PMF.pure (x a) := by
            exact PMF.map_const
              (p := finiteVolumeAssignmentPMF
                (M := M'.toInfiniteGroundMLNSpec)
                ({i.1} : Region Atom) η hZ)
              (b := x a)

/-- The one-site heat-bath kernel is recovered from its Boolean marginal at the
updated site by re-inserting that Boolean into the fixed outside assignment. -/
theorem singleSiteHeatBathKernelPMF_eq_map_eval_map_mergeAssignments
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ) :
    M.singleSiteHeatBathKernelPMF i ξ x =
      ((M.singleSiteHeatBathKernelPMF i ξ x).map (fun y => y i)).map
        (fun b =>
          mergeAssignments (Atom := Atom)
            (singletonAssignment (Atom := Atom) i.1 b)
            (restrictOutsideAssignment (Atom := Atom) x)) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  let r :=
    finiteVolumeAssignmentPMF
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ
  let g : LocalAssignment Atom ({i.1} : Region Atom) → LocalAssignment Atom Δ :=
    fun s =>
      mergeAssignments (Atom := Atom) s
        (restrictOutsideAssignment (Atom := Atom) x)
  let e : LocalAssignment Atom ({i.1} : Region Atom) → Bool :=
    fun s => s ⟨i.1, by simp⟩
  let h : Bool → LocalAssignment Atom Δ :=
    fun b =>
      mergeAssignments (Atom := Atom)
        (singletonAssignment (Atom := Atom) i.1 b)
        (restrictOutsideAssignment (Atom := Atom) x)
  have hk : M.singleSiteHeatBathKernelPMF i ξ x = r.map g := by
    simp [M.singleSiteHeatBathKernelPMF_eq_map_mergeAssignments, M', η, r, g]
  have hmap_eval : (r.map g).map (fun y => y i) = r.map e := by
    calc
      (r.map g).map (fun y => y i) = r.map ((fun y => y i) ∘ g) := by
        simpa using (PMF.map_comp (p := r) (f := g) (fun y => y i))
      _ = r.map e := by
        congr 1
        funext s
        simp [e, g, mergeAssignments]
  have hroundtrip : (r.map e).map h = r.map g := by
    calc
      (r.map e).map h = r.map (h ∘ e) := by
        simpa using (PMF.map_comp (p := r) (f := e) h)
      _ = r.map g := by
        congr 1
        funext s
        ext a
        by_cases ha : a.1 ∈ ({i.1} : Region Atom)
        · have hai : a.1 = i.1 := by
            simpa using ha
          have hsub : a = i := by
            apply Subtype.ext
            exact hai
          subst hsub
          simp [h, e, g, singletonAssignment, mergeAssignments]
        · have hai : a.1 ∉ ({i.1} : Region Atom) := by
            simpa using ha
          simp [h, e, g, mergeAssignments, restrictOutsideAssignment, hai]
  calc
    M.singleSiteHeatBathKernelPMF i ξ x = r.map g := hk
    _ = (r.map e).map h := hroundtrip.symm
    _ = ((r.map g).map (fun y => y i)).map h := by
          rw [hmap_eval]
    _ =
      ((M.singleSiteHeatBathKernelPMF i ξ x).map (fun y => y i)).map
        (fun b =>
          mergeAssignments (Atom := Atom)
            (singletonAssignment (Atom := Atom) i.1 b)
            (restrictOutsideAssignment (Atom := Atom) x)) := by
          simp [hk, h]

/-- The corresponding one-step single-site heat-bath update operator on PMFs of
finite-region assignments. -/
noncomputable def singleSiteHeatBathUpdatePMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (p : PMF (LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Δ) :=
  p.bind (M.singleSiteHeatBathKernelPMF i ξ)

/-- The one-site heat-bath kernel computes the singleton finite-volume Gibbs
kernel on cylinder events over `Δ`. -/
theorem singleSiteHeatBathKernelPMF_toMeasure_apply
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ)
    (S : Set (LocalAssignment Atom Δ))
    (hS : MeasurableSet S) :
    (M.singleSiteHeatBathKernelPMF i ξ x).toMeasure S =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M.toStrictlyPositiveInfiniteGroundMLNSpec
        ({i.1} : Region Atom) (patch Δ x ξ)
        (MeasureTheory.cylinder Δ S) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  rw [show M.singleSiteHeatBathKernelPMF i ξ x =
      (finiteVolumeWorldPMF
        (M := M'.toInfiniteGroundMLNSpec)
        ({i.1} : Region Atom) η hZ).map
        (worldRestriction Δ) by
      simp [singleSiteHeatBathKernelPMF, M', η]]
  rw [PMF.toMeasure_map_apply
    (p := finiteVolumeWorldPMF
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ)
    (f := worldRestriction Δ)
    (s := S)
    (hf := measurable_worldRestriction Δ)
    (hs := hS)]
  change PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ ((worldRestriction Δ) ⁻¹' S) =
    PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ (MeasureTheory.cylinder Δ S)
  have hrestrict : worldRestriction Δ = Finset.restrict Δ := by
    funext ω a
    rfl
  simp [MeasureTheory.cylinder, hrestrict]

/-- Averaging the one-site heat-bath kernel against an input PMF yields the
expected singleton finite-volume Gibbs kernel on cylinder events. -/
theorem singleSiteHeatBathUpdatePMF_toMeasure_apply
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (p : PMF (LocalAssignment Atom Δ))
    (S : Set (LocalAssignment Atom Δ))
    (hS : MeasurableSet S) :
    (M.singleSiteHeatBathUpdatePMF i ξ p).toMeasure S =
      ∑' x : LocalAssignment Atom Δ,
        p x *
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
            M.toStrictlyPositiveInfiniteGroundMLNSpec
            ({i.1} : Region Atom) (patch Δ x ξ)
            (MeasureTheory.cylinder Δ S) := by
  rw [singleSiteHeatBathUpdatePMF]
  rw [PMF.toMeasure_bind_apply (s := S) (hs := hS)]
  refine tsum_congr fun x => ?_
  rw [M.singleSiteHeatBathKernelPMF_toMeasure_apply i ξ x S hS]

/-- On the full patched region, the finite-volume world measure of a cylinder
event is exactly the corresponding finite-volume assignment PMF mass. -/
theorem finiteVolumeWorldMeasure_cylinder_region_eq_assignmentPMF_toMeasure
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Δ : Region Atom)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0)
    (S : Set (LocalAssignment Atom Δ))
    (hS : MeasurableSet S) :
    PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
      (M := M) Δ ξ hZ (MeasureTheory.cylinder Δ S) =
      (finiteVolumeAssignmentPMF M Δ ξ hZ).toMeasure S := by
  unfold PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
    finiteVolumeWorldPMF
  rw [PMF.toMeasure_map_apply
    (p := finiteVolumeAssignmentPMF M Δ ξ hZ)
    (f := fun x : LocalAssignment Atom Δ => patch Δ x ξ)
    (s := MeasureTheory.cylinder Δ S)
    (hf := measurable_patch Δ ξ)
    (hs := hS.cylinder Δ)]
  rw [preimage_cylinder_patch (ξ := ξ) (S := S)]

/-- At the updated site itself, the one-site heat-bath kernel has exactly the
singleton Gibbs true-marginal determined by the patched boundary condition. -/
theorem singleSiteHeatBathKernelPMF_true_prob
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Δ) :
    ((M.singleSiteHeatBathKernelPMF i ξ x).toMeasure
      {y : LocalAssignment Atom Δ | y i = true}).toReal =
      M.singletonKernelTrueProb i.1 (patch Δ x ξ) := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let η := patch Δ x ξ
  let hZ :
      M'.toInfiniteGroundMLNSpec.finiteVolumePartition ({i.1} : Region Atom) η ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero
      M' ({i.1} : Region Atom) η
  let SΔ : Set (LocalAssignment Atom Δ) := {y | y i = true}
  have hSΔ : MeasurableSet SΔ := by
    exact (Set.to_countable SΔ).measurableSet
  have hpre :
      (fun s : LocalAssignment Atom ({i.1} : Region Atom) =>
        mergeAssignments (Atom := Atom) s
          (restrictOutsideAssignment (Atom := Atom) x)) ⁻¹' SΔ =
        singletonTrueAssignmentSet i.1 := by
    ext s
    simp [SΔ, singletonTrueAssignmentSet, mergeAssignments]
  have hmap :
      (M.singleSiteHeatBathKernelPMF i ξ x).toMeasure SΔ =
        (finiteVolumeAssignmentPMF
          (M := M'.toInfiniteGroundMLNSpec)
          ({i.1} : Region Atom) η hZ).toMeasure
            (singletonTrueAssignmentSet i.1) := by
    rw [M.singleSiteHeatBathKernelPMF_eq_map_mergeAssignments (i := i) (ξ := ξ) (x := x)]
    rw [PMF.toMeasure_map_apply
      (p := finiteVolumeAssignmentPMF
        (M := M'.toInfiniteGroundMLNSpec)
        ({i.1} : Region Atom) η hZ)
      (f := fun s : LocalAssignment Atom ({i.1} : Region Atom) =>
        mergeAssignments (Atom := Atom) s
          (restrictOutsideAssignment (Atom := Atom) x))
      (s := SΔ)
      (hf := by
        classical
        refine measurable_pi_lambda _ ?_
        intro a
        by_cases ha : a.1 ∈ ({i.1} : Region Atom)
        · have hai : a.1 = i.1 := by
            simpa using ha
          have hcoord :
              Measurable
                (fun c : LocalAssignment Atom ({i.1} : Region Atom) =>
                  c ⟨i.1, by simp⟩) := by
                simpa using
                  (measurable_pi_apply
                    (a := (⟨i.1, by simp⟩ : RegionAtom Atom ({i.1} : Region Atom))))
          simpa [mergeAssignments, hai] using hcoord
        · simp [mergeAssignments, restrictOutsideAssignment, ha])
      (hs := hSΔ)]
    simp [hpre]
  have hregion :
      PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
        (M := M'.toInfiniteGroundMLNSpec)
        ({i.1} : Region Atom) η hZ
        (MeasureTheory.cylinder ({i.1} : Region Atom) (singletonTrueAssignmentSet i.1)) =
      (finiteVolumeAssignmentPMF
        (M := M'.toInfiniteGroundMLNSpec)
        ({i.1} : Region Atom) η hZ).toMeasure
          (singletonTrueAssignmentSet i.1) := by
    exact finiteVolumeWorldMeasure_cylinder_region_eq_assignmentPMF_toMeasure
      (M := M'.toInfiniteGroundMLNSpec)
      ({i.1} : Region Atom) η hZ
      (singletonTrueAssignmentSet i.1)
      (measurableSet_singletonTrueAssignmentSet i.1)
  calc
    ((M.singleSiteHeatBathKernelPMF i ξ x).toMeasure SΔ).toReal
      = ENNReal.toReal
          ((finiteVolumeAssignmentPMF
            (M := M'.toInfiniteGroundMLNSpec)
            ({i.1} : Region Atom) η hZ).toMeasure
              (singletonTrueAssignmentSet i.1)) := by
                rw [hmap]
    _ = ENNReal.toReal
          (PLNMarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
            (M := M'.toInfiniteGroundMLNSpec)
            ({i.1} : Region Atom) η hZ
            (MeasureTheory.cylinder ({i.1} : Region Atom)
              (singletonTrueAssignmentSet i.1))) := by
                rw [← hregion]
    _ = M.singletonKernelTrueProb i.1 (patch Δ x ξ) := by
          simp [singletonKernelTrueProb, M', η,
            StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure]

theorem singleSiteHeatBathKernelPMF_map_eval_totalVariation_eq_trueSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    pmfTotalVariation
      ((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i))
      ((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)) =
      M.singletonKernelTrueSensitivity i.1 (patch Δ x ξ) (patch Δ y ξ) := by
  have hx :
      ENNReal.toReal (((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)) true) =
        M.singletonKernelTrueProb i.1 (patch Δ x ξ) := by
    have hmap :
        (((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)).toMeasure ({true} : Set Bool)) =
          ((M.singleSiteHeatBathKernelPMF i ξ x).toMeasure
            {z : LocalAssignment Atom Δ | z i = true}) := by
      simpa using
        (PMF.toMeasure_map_apply
          (p := M.singleSiteHeatBathKernelPMF i ξ x)
          (f := fun z => z i)
          (s := ({true} : Set Bool))
          (hf := by
            classical
            exact Measurable.of_discrete)
          (hs := MeasurableSet.singleton true))
    calc
      ENNReal.toReal (((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)) true)
        = (((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)).toMeasure
            ({true} : Set Bool)).toReal := by
              rw [← ((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)).toMeasure_apply_singleton
                true (MeasurableSet.singleton true)]
      _ = ((M.singleSiteHeatBathKernelPMF i ξ x).toMeasure
            {z : LocalAssignment Atom Δ | z i = true}).toReal := by
              rw [hmap]
      _ = M.singletonKernelTrueProb i.1 (patch Δ x ξ) := by
              exact M.singleSiteHeatBathKernelPMF_true_prob i ξ x
  have hy :
      ENNReal.toReal (((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)) true) =
        M.singletonKernelTrueProb i.1 (patch Δ y ξ) := by
    have hmap :
        (((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)).toMeasure ({true} : Set Bool)) =
          ((M.singleSiteHeatBathKernelPMF i ξ y).toMeasure
            {z : LocalAssignment Atom Δ | z i = true}) := by
      simpa using
        (PMF.toMeasure_map_apply
          (p := M.singleSiteHeatBathKernelPMF i ξ y)
          (f := fun z => z i)
          (s := ({true} : Set Bool))
          (hf := by
            classical
            exact Measurable.of_discrete)
          (hs := MeasurableSet.singleton true))
    calc
      ENNReal.toReal (((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)) true)
        = (((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)).toMeasure
            ({true} : Set Bool)).toReal := by
              rw [← ((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)).toMeasure_apply_singleton
                true (MeasurableSet.singleton true)]
      _ = ((M.singleSiteHeatBathKernelPMF i ξ y).toMeasure
            {z : LocalAssignment Atom Δ | z i = true}).toReal := by
              rw [hmap]
      _ = M.singletonKernelTrueProb i.1 (patch Δ y ξ) := by
              exact M.singleSiteHeatBathKernelPMF_true_prob i ξ y
  rw [pmfTotalVariation_eq_abs_sub_apply_true]
  rw [hx, hy]
  rfl

/-- A maximal coupling of the Bool marginals at the updated site, lifted back
to full assignments by re-inserting that Bool into the frozen outside
configuration on each side. -/
noncomputable def singleSiteHeatBathKernelCouplingPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ) :=
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  (pmfMaximalCoupling px py).map (fun zz =>
    ( mergeAssignments (Atom := Atom)
        (singletonAssignment (Atom := Atom) i.1 zz.1)
        (restrictOutsideAssignment (Atom := Atom) x)
    , mergeAssignments (Atom := Atom)
        (singletonAssignment (Atom := Atom) i.1 zz.2)
        (restrictOutsideAssignment (Atom := Atom) y)))

theorem singleSiteHeatBathKernelCouplingPMF_map_fst
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map Prod.fst =
      M.singleSiteHeatBathKernelPMF i ξ x := by
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  let lift : Bool × Bool → LocalAssignment Atom Δ × LocalAssignment Atom Δ :=
    fun zz =>
      ( mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.1)
          (restrictOutsideAssignment (Atom := Atom) x)
      , mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.2)
          (restrictOutsideAssignment (Atom := Atom) y))
  calc
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map Prod.fst
      = ((pmfMaximalCoupling px py).map lift).map Prod.fst := by
          simp [singleSiteHeatBathKernelCouplingPMF, px, py, lift]
    _ = (pmfMaximalCoupling px py).map
          (fun zz =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 zz.1)
              (restrictOutsideAssignment (Atom := Atom) x)) := by
          simpa [lift] using
            (PMF.map_comp (p := pmfMaximalCoupling px py) (f := lift) Prod.fst)
    _ = (PMF.map Prod.fst (pmfMaximalCoupling px py)).map
          (fun b =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 b)
              (restrictOutsideAssignment (Atom := Atom) x)) := by
          symm
          simpa using
            (PMF.map_comp
              (p := pmfMaximalCoupling px py)
              (f := Prod.fst)
              (fun b =>
                mergeAssignments (Atom := Atom)
                  (singletonAssignment (Atom := Atom) i.1 b)
                  (restrictOutsideAssignment (Atom := Atom) x)))
    _ = px.map
          (fun b =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 b)
              (restrictOutsideAssignment (Atom := Atom) x)) := by
          rw [pmfMaximalCoupling_map_fst]
    _ = M.singleSiteHeatBathKernelPMF i ξ x := by
          simpa [px] using
            (M.singleSiteHeatBathKernelPMF_eq_map_eval_map_mergeAssignments
              (i := i) (ξ := ξ) (x := x)).symm

theorem singleSiteHeatBathKernelCouplingPMF_map_snd
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map Prod.snd =
      M.singleSiteHeatBathKernelPMF i ξ y := by
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  let lift : Bool × Bool → LocalAssignment Atom Δ × LocalAssignment Atom Δ :=
    fun zz =>
      ( mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.1)
          (restrictOutsideAssignment (Atom := Atom) x)
      , mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.2)
          (restrictOutsideAssignment (Atom := Atom) y))
  calc
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map Prod.snd
      = ((pmfMaximalCoupling px py).map lift).map Prod.snd := by
          simp [singleSiteHeatBathKernelCouplingPMF, px, py, lift]
    _ = (pmfMaximalCoupling px py).map
          (fun zz =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 zz.2)
              (restrictOutsideAssignment (Atom := Atom) y)) := by
          simpa [lift] using
            (PMF.map_comp (p := pmfMaximalCoupling px py) (f := lift) Prod.snd)
    _ = (PMF.map Prod.snd (pmfMaximalCoupling px py)).map
          (fun b =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 b)
              (restrictOutsideAssignment (Atom := Atom) y)) := by
          symm
          simpa using
            (PMF.map_comp
              (p := pmfMaximalCoupling px py)
              (f := Prod.snd)
              (fun b =>
                mergeAssignments (Atom := Atom)
                  (singletonAssignment (Atom := Atom) i.1 b)
                  (restrictOutsideAssignment (Atom := Atom) y)))
    _ = py.map
          (fun b =>
            mergeAssignments (Atom := Atom)
              (singletonAssignment (Atom := Atom) i.1 b)
              (restrictOutsideAssignment (Atom := Atom) y)) := by
          rw [pmfMaximalCoupling_map_snd]
    _ = M.singleSiteHeatBathKernelPMF i ξ y := by
          simpa [py] using
            (M.singleSiteHeatBathKernelPMF_eq_map_eval_map_mergeAssignments
              (i := i) (ξ := ξ) (x := y)).symm

theorem disagreementIndicator_eq_ite_regionAtom
    {Δ : Region Atom}
    (x y : LocalAssignment Atom Δ)
    (a : RegionAtom Atom Δ) :
    disagreementIndicator x y a.1 = if x a = y a then 0 else 1 := by
  by_cases hxy : x a = y a
  · have hnot : a.1 ∉ disagreementRegion x y := by
      intro hmem
      rcases (mem_disagreementRegion_iff x y).1 hmem with ⟨ha, hneq⟩
      exact hneq (by simpa using hxy)
    simp [disagreementIndicator, hnot, hxy]
  · have hmem : a.1 ∈ disagreementRegion x y := by
      exact (mem_disagreementRegion_iff x y).2 ⟨a.2, by simpa using hxy⟩
    simp [disagreementIndicator, hmem, hxy]

theorem singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map
        (fun z => (z.1 a, z.2 a)) =
      PMF.pure (x a, y a) := by
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  let lift : Bool × Bool → LocalAssignment Atom Δ × LocalAssignment Atom Δ :=
    fun zz =>
      ( mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.1)
          (restrictOutsideAssignment (Atom := Atom) x)
      , mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.2)
          (restrictOutsideAssignment (Atom := Atom) y))
  calc
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map (fun z => (z.1 a, z.2 a))
      = ((pmfMaximalCoupling px py).map lift).map (fun z => (z.1 a, z.2 a)) := by
          simp [singleSiteHeatBathKernelCouplingPMF, px, py, lift]
    _ = (pmfMaximalCoupling px py).map
          (fun zz =>
            ((mergeAssignments (Atom := Atom)
                (singletonAssignment (Atom := Atom) i.1 zz.1)
                (restrictOutsideAssignment (Atom := Atom) x)) a,
             (mergeAssignments (Atom := Atom)
                (singletonAssignment (Atom := Atom) i.1 zz.2)
                (restrictOutsideAssignment (Atom := Atom) y)) a)) := by
          simpa [lift] using
            (PMF.map_comp (p := pmfMaximalCoupling px py) (f := lift)
              (fun z => (z.1 a, z.2 a)))
    _ = (pmfMaximalCoupling px py).map (Function.const _ (x a, y a)) := by
          congr 1
          funext zz
          simp [mergeAssignments, restrictOutsideAssignment, ha]
    _ = PMF.pure (x a, y a) := by
          exact PMF.map_const (p := pmfMaximalCoupling px py) (b := (x a, y a))

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathKernelCoupling_eq_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathKernelCouplingPMF i ξ x y) a.1 =
      disagreementIndicator x y a.1 := by
  let evalPair :
      (LocalAssignment Atom Δ × LocalAssignment Atom Δ) → Bool × Bool :=
    fun z => (z.1 a, z.2 a)
  have hmap :
      (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map evalPair =
        PMF.pure (x a, y a) :=
    M.singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_of_ne i a ha ξ x y
  calc
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathKernelCouplingPMF i ξ x y) a.1
      =
        ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          (if (evalPair z).1 = (evalPair z).2 then (0 : ℝ) else 1) *
            ENNReal.toReal ((M.singleSiteHeatBathKernelCouplingPMF i ξ x y) z) := by
          unfold finiteRegionCouplingExpectedDisagreement
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [disagreementIndicator_eq_ite_regionAtom (x := z.1) (y := z.2) (a := a)]
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal (((M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map evalPair) u) := by
          symm
          exact sum_mul_toReal_map_eq
            (p := M.singleSiteHeatBathKernelCouplingPMF i ξ x y)
            (h := evalPair)
            (f := fun u : Bool × Bool => if u.1 = u.2 then (0 : ℝ) else 1)
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal ((PMF.pure (x a, y a)) u) := by
          rw [hmap]
    _ = disagreementIndicator x y a.1 := by
          by_cases hxy : x a = y a
          · rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
            simp [PMF.pure_apply, disagreementIndicator_eq_ite_regionAtom (x := x) (y := y) (a := a), hxy]
          · rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
            cases hxa : x a <;> cases hya : y a
            · exfalso
              exact hxy (by simp [hxa, hya])
            · simp [PMF.pure_apply, disagreementIndicator_eq_ite_regionAtom (x := x) (y := y) (a := a), hxa, hya]
            · simp [PMF.pure_apply, disagreementIndicator_eq_ite_regionAtom (x := x) (y := y) (a := a), hxa, hya]
            · exfalso
              exact hxy (by simp [hxa, hya])

theorem singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_updatedSite
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map
        (fun z => (z.1 i, z.2 i)) =
      pmfMaximalCoupling
        ((M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i))
        ((M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)) := by
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  let lift : Bool × Bool → LocalAssignment Atom Δ × LocalAssignment Atom Δ :=
    fun zz =>
      ( mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.1)
          (restrictOutsideAssignment (Atom := Atom) x)
      , mergeAssignments (Atom := Atom)
          (singletonAssignment (Atom := Atom) i.1 zz.2)
          (restrictOutsideAssignment (Atom := Atom) y))
  calc
    (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map (fun z => (z.1 i, z.2 i))
      = ((pmfMaximalCoupling px py).map lift).map (fun z => (z.1 i, z.2 i)) := by
          simp [singleSiteHeatBathKernelCouplingPMF, px, py, lift]
    _ = (pmfMaximalCoupling px py).map
          (fun zz =>
            ((mergeAssignments (Atom := Atom)
                (singletonAssignment (Atom := Atom) i.1 zz.1)
                (restrictOutsideAssignment (Atom := Atom) x)) i,
             (mergeAssignments (Atom := Atom)
                (singletonAssignment (Atom := Atom) i.1 zz.2)
                (restrictOutsideAssignment (Atom := Atom) y)) i)) := by
          simpa [lift] using
            (PMF.map_comp (p := pmfMaximalCoupling px py) (f := lift)
              (fun z => (z.1 i, z.2 i)))
    _ = (pmfMaximalCoupling px py).map id := by
          congr 1
          funext zz
          simp [mergeAssignments, singletonAssignment]
    _ = pmfMaximalCoupling px py := by
          simpa using (PMF.map_id (p := pmfMaximalCoupling px py))

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathKernelCoupling_eq_trueSensitivity
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (x y : LocalAssignment Atom Δ) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathKernelCouplingPMF i ξ x y) i.1 =
      M.singletonKernelTrueSensitivity i.1 (patch Δ x ξ) (patch Δ y ξ) := by
  let px := (M.singleSiteHeatBathKernelPMF i ξ x).map (fun z => z i)
  let py := (M.singleSiteHeatBathKernelPMF i ξ y).map (fun z => z i)
  let evalPair :
      (LocalAssignment Atom Δ × LocalAssignment Atom Δ) → Bool × Bool :=
    fun z => (z.1 i, z.2 i)
  have hmap :
      (M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map evalPair =
        pmfMaximalCoupling px py :=
    M.singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_updatedSite i ξ x y
  calc
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathKernelCouplingPMF i ξ x y) i.1
      =
        ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          (if (evalPair z).1 = (evalPair z).2 then (0 : ℝ) else 1) *
            ENNReal.toReal ((M.singleSiteHeatBathKernelCouplingPMF i ξ x y) z) := by
          unfold finiteRegionCouplingExpectedDisagreement
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [disagreementIndicator_eq_ite_regionAtom (x := z.1) (y := z.2) (a := i)]
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal (((M.singleSiteHeatBathKernelCouplingPMF i ξ x y).map evalPair) u) := by
          symm
          exact sum_mul_toReal_map_eq
            (p := M.singleSiteHeatBathKernelCouplingPMF i ξ x y)
            (h := evalPair)
            (f := fun u : Bool × Bool => if u.1 = u.2 then (0 : ℝ) else 1)
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal ((pmfMaximalCoupling px py) u) := by
          rw [hmap]
    _ = pmfTotalVariation px py := by
          exact pmfMaximalCoupling_disagreementProbability_eq_totalVariation px py
    _ = M.singletonKernelTrueSensitivity i.1 (patch Δ x ξ) (patch Δ y ξ) := by
          exact M.singleSiteHeatBathKernelPMF_map_eval_totalVariation_eq_trueSensitivity i ξ x y

theorem finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : RegionAtom Atom Δ) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a.1 =
      ∑ u : Bool × Bool,
        (if u.1 = u.2 then (0 : ℝ) else 1) *
          ENNReal.toReal ((q.map (fun z => (z.1 a, z.2 a))) u) := by
  calc
    finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a.1
      =
        ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          (if z.1 a = z.2 a then (0 : ℝ) else 1) * ENNReal.toReal (q z) := by
          unfold finiteRegionCouplingExpectedDisagreement
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [disagreementIndicator_eq_ite_regionAtom (x := z.1) (y := z.2) (a := a)]
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal ((q.map (fun z => (z.1 a, z.2 a))) u) := by
          symm
          exact sum_mul_toReal_map_eq
            (p := q)
            (h := fun z => (z.1 a, z.2 a))
            (f := fun u : Bool × Bool => if u.1 = u.2 then (0 : ℝ) else 1)

/-- One-site heat-bath update lifted from an input coupling of local
assignments by binding the explicit kernel coupling at each paired state. -/
noncomputable def singleSiteHeatBathUpdateCouplingPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ) :=
  q.bind (fun z => M.singleSiteHeatBathKernelCouplingPMF i ξ z.1 z.2)

theorem singleSiteHeatBathUpdateCouplingPMF_map_fst
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map Prod.fst =
      M.singleSiteHeatBathUpdatePMF i ξ (q.map Prod.fst) := by
  calc
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map Prod.fst
      = q.bind
          (fun z =>
            (M.singleSiteHeatBathKernelCouplingPMF i ξ z.1 z.2).map Prod.fst) := by
            simp [singleSiteHeatBathUpdateCouplingPMF, PMF.map_bind]
    _ = q.bind (fun z => M.singleSiteHeatBathKernelPMF i ξ z.1) := by
          congr 1
          funext z
          exact M.singleSiteHeatBathKernelCouplingPMF_map_fst i ξ z.1 z.2
    _ = (q.map Prod.fst).bind (M.singleSiteHeatBathKernelPMF i ξ) := by
          rw [PMF.bind_map]
          rfl
    _ = M.singleSiteHeatBathUpdatePMF i ξ (q.map Prod.fst) := by
          rfl

theorem singleSiteHeatBathUpdateCouplingPMF_map_snd
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map Prod.snd =
      M.singleSiteHeatBathUpdatePMF i ξ (q.map Prod.snd) := by
  calc
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map Prod.snd
      = q.bind
          (fun z =>
            (M.singleSiteHeatBathKernelCouplingPMF i ξ z.1 z.2).map Prod.snd) := by
            simp [singleSiteHeatBathUpdateCouplingPMF, PMF.map_bind]
    _ = q.bind (fun z => M.singleSiteHeatBathKernelPMF i ξ z.2) := by
          congr 1
          funext z
          exact M.singleSiteHeatBathKernelCouplingPMF_map_snd i ξ z.1 z.2
    _ = (q.map Prod.snd).bind (M.singleSiteHeatBathKernelPMF i ξ) := by
          rw [PMF.bind_map]
          rfl
    _ = M.singleSiteHeatBathUpdatePMF i ξ (q.map Prod.snd) := by
          rfl

theorem singleSiteHeatBathUpdateCouplingPMF_map_eval_pair_eq_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map (fun z => (z.1 a, z.2 a)) =
      q.map (fun z => (z.1 a, z.2 a)) := by
  calc
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map (fun z => (z.1 a, z.2 a))
      = q.bind
          (fun z =>
            (M.singleSiteHeatBathKernelCouplingPMF i ξ z.1 z.2).map
              (fun z' => (z'.1 a, z'.2 a))) := by
            simp [singleSiteHeatBathUpdateCouplingPMF, PMF.map_bind]
    _ = q.bind (fun z => PMF.pure (z.1 a, z.2 a)) := by
          congr 1
          funext z
          exact M.singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_of_ne i a ha ξ z.1 z.2
    _ = q.map (fun z => (z.1 a, z.2 a)) := by
          simpa using
            (PMF.bind_pure_comp
              (p := q)
              (f := fun z : LocalAssignment Atom Δ × LocalAssignment Atom Δ => (z.1 a, z.2 a)))

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_eq_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathUpdateCouplingPMF i ξ q) a.1 =
      finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a.1 := by
  rw [finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair
    (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q) (a := a)]
  rw [M.singleSiteHeatBathUpdateCouplingPMF_map_eval_pair_eq_of_ne i a ha ξ q]
  rw [finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair (q := q) (a := a)]

theorem singleSiteHeatBathUpdateCouplingPMF_map_eval_pair_updatedSite
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map (fun z => (z.1 i, z.2 i)) =
      q.bind (fun z =>
        pmfMaximalCoupling
          ((M.singleSiteHeatBathKernelPMF i ξ z.1).map (fun z' => z' i))
          ((M.singleSiteHeatBathKernelPMF i ξ z.2).map (fun z' => z' i))) := by
  calc
    (M.singleSiteHeatBathUpdateCouplingPMF i ξ q).map (fun z => (z.1 i, z.2 i))
      = q.bind
          (fun z =>
            (M.singleSiteHeatBathKernelCouplingPMF i ξ z.1 z.2).map
              (fun z' => (z'.1 i, z'.2 i))) := by
            simp [singleSiteHeatBathUpdateCouplingPMF, PMF.map_bind]
    _ = q.bind
          (fun z =>
            pmfMaximalCoupling
              ((M.singleSiteHeatBathKernelPMF i ξ z.1).map (fun z' => z' i))
              ((M.singleSiteHeatBathKernelPMF i ξ z.2).map (fun z' => z' i))) := by
          congr 1
          funext z
          exact M.singleSiteHeatBathKernelCouplingPMF_map_eval_pair_eq_updatedSite i ξ z.1 z.2

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_eq_updatedSite
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathUpdateCouplingPMF i ξ q) i.1 =
      ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
        M.singletonKernelTrueSensitivity i.1 (patch Δ z.1 ξ) (patch Δ z.2 ξ) *
          ENNReal.toReal (q z) := by
  rw [finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair
    (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q) (a := i)]
  rw [M.singleSiteHeatBathUpdateCouplingPMF_map_eval_pair_updatedSite i ξ q]
  rw [sum_mul_toReal_bind_eq]
  refine Finset.sum_congr rfl ?_
  intro z hz
  rw [pmfMaximalCoupling_disagreementProbability_eq_totalVariation]
  rw [M.singleSiteHeatBathKernelPMF_map_eval_totalVariation_eq_trueSensitivity i ξ z.1 z.2]

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_le_updatedSite
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathUpdateCouplingPMF i ξ q) i.1 ≤
      M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity ξ q i.1 := by
  rw [M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_eq_updatedSite i ξ q]
  unfold finiteRegionCouplingExpectedBernoulliUpdateSensitivity
  refine Finset.sum_le_sum ?_
  intro z hz
  have htrue_le_l1 :
      M.singletonKernelTrueSensitivity i.1 (patch Δ z.1 ξ) (patch Δ z.2 ξ) ≤
        M.singletonKernelBernoulliL1Sensitivity i.1 (patch Δ z.1 ξ) (patch Δ z.2 ξ) := by
    have hnonneg :=
      M.singletonKernelTrueSensitivity_nonneg i.1 (patch Δ z.1 ξ) (patch Δ z.2 ξ)
    rw [M.singletonKernelBernoulliL1Sensitivity_eq_two_mul_trueSensitivity
      i.1 (patch Δ z.1 ξ) (patch Δ z.2 ξ)]
    nlinarith
  exact mul_le_mul_of_nonneg_right htrue_le_l1 ENNReal.toReal_nonneg

theorem finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_le_pairwiseDobrushinOperator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (M.singleSiteHeatBathUpdateCouplingPMF i ξ q) i.1 ≤
      M.pairwiseDobrushinOperator Δ (finiteRegionCouplingExpectedDisagreement q) i.1 := by
  refine le_trans
    (M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_le_updatedSite i ξ q)
    (M.finiteRegionCouplingExpectedBernoulliUpdateSensitivity_le_pairwiseDobrushinOperator
      (ξ := ξ) (q := q) i.1)

/-- The updated site's true-marginal after one heat-bath step is the expected
singleton Gibbs kernel against the input finite-region assignment PMF. -/
theorem singleSiteHeatBathUpdatePMF_true_prob
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (p : PMF (LocalAssignment Atom Δ)) :
    (((M.singleSiteHeatBathUpdatePMF i ξ p).toMeasure
      {y : LocalAssignment Atom Δ | y i = true}).toReal) =
      ∑ x : LocalAssignment Atom Δ,
        M.singletonKernelTrueProb i.1 (patch Δ x ξ) * ENNReal.toReal (p x) := by
  let SΔ : Set (LocalAssignment Atom Δ) := {y | y i = true}
  have hSΔ : MeasurableSet SΔ := by
    exact (Set.to_countable SΔ).measurableSet
  rw [singleSiteHeatBathUpdatePMF]
  rw [PMF.toMeasure_bind_apply (s := SΔ) (hs := hSΔ)]
  rw [tsum_fintype]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro x hx
    rw [ENNReal.toReal_mul]
    calc
      ENNReal.toReal (p x) * ((M.singleSiteHeatBathKernelPMF i ξ x).toMeasure SΔ).toReal
        = ENNReal.toReal (p x) *
            M.singletonKernelTrueProb i.1 (patch Δ x ξ) := by
              rw [M.singleSiteHeatBathKernelPMF_true_prob (i := i) (ξ := ξ) (x := x)]
      _ = M.singletonKernelTrueProb i.1 (patch Δ x ξ) * ENNReal.toReal (p x) := by
            ring
  · intro x hx
    exact ENNReal.mul_ne_top (p.apply_ne_top x) (measure_ne_top _ _)

/-- A one-site heat-bath update leaves every other coordinate marginal
unchanged. -/
theorem singleSiteHeatBathUpdatePMF_map_eval_eq_of_ne
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i a : RegionAtom Atom Δ)
    (ha : a.1 ≠ i.1)
    (ξ : BoundaryCondition Atom)
    (p : PMF (LocalAssignment Atom Δ)) :
    (M.singleSiteHeatBathUpdatePMF i ξ p).map (fun y => y a) =
      p.map (fun x => x a) := by
  calc
    (M.singleSiteHeatBathUpdatePMF i ξ p).map (fun y => y a)
      = p.bind (fun x => (M.singleSiteHeatBathKernelPMF i ξ x).map (fun y => y a)) := by
          simp [singleSiteHeatBathUpdatePMF, PMF.map_bind]
    _ = p.bind (fun x => PMF.pure (x a)) := by
          congr 1
          funext x
          exact M.singleSiteHeatBathKernelPMF_map_eval_eq_pure_of_ne i a ha ξ x
    _ = p.map (fun x => x a) := by
          simpa using
            (PMF.bind_pure_comp
              (p := p)
              (f := fun x : LocalAssignment Atom Δ => x a))

/-- The finite-volume Gibbs PMF on `Δ` is a fixed point of every one-site
heat-bath update `Q_t` with `t ∈ Δ`. -/
theorem finiteVolumeAssignmentPMF_singleSiteHeatBathUpdatePMF_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom) :
    let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
    let hZΔ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M' Δ ξ
    M.singleSiteHeatBathUpdatePMF i ξ
      (finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ) =
      finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let hZΔ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M' Δ ξ
  let pΔ := finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ
  have hsubset : ({i.1} : Region Atom) ⊆ Δ := by
    intro a ha
    have ha' : a = i.1 := by
      simpa using ha
    have hmem : a ∈ Δ := by
      cases ha'
      exact i.2
    exact hmem
  ext y
  have hsingleton : MeasurableSet ({y} : Set (LocalAssignment Atom Δ)) :=
    MeasurableSet.singleton y
  have hupdate :=
    M.singleSiteHeatBathUpdatePMF_toMeasure_apply i ξ pΔ ({y} : Set (LocalAssignment Atom Δ))
      hsingleton
  rw [tsum_fintype] at hupdate
  have hdlr :
      ∑ x : LocalAssignment Atom Δ,
        pΔ x *
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
            M' ({i.1} : Region Atom) (patch Δ x ξ)
            (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) =
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
          M' Δ ξ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
    simpa [pΔ] using
      (finiteVolumeAssignmentPMF_subregion_cylinder_dlr
        (M := M') (hΛΔ := hsubset) (ξ := ξ)
        (I := Δ) (S := ({y} : Set (LocalAssignment Atom Δ))) hsingleton)
  rw [hdlr] at hupdate
  have hregion :
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
        M' Δ ξ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) =
        pΔ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) := by
    simpa [pΔ] using
      (finiteVolumeWorldMeasure_cylinder_region_eq_assignmentPMF_toMeasure
        (M := M'.toInfiniteGroundMLNSpec) Δ ξ hZΔ ({y} : Set (LocalAssignment Atom Δ))
        hsingleton)
  rw [hregion] at hupdate
  simpa [pΔ, PMF.toMeasure_apply_singleton] using hupdate

/-- Dobrushin's finite sweep operator: apply the one-site heat-bath updates
through a fixed enumeration of the finite region. -/
noncomputable def finiteRegionHeatBathSweepPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (p : PMF (LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Δ) :=
  (Δ.attach.toList).foldl (fun q i => M.singleSiteHeatBathUpdatePMF i ξ q) p

/-- The finite-volume Gibbs PMF on `Δ` is a fixed point of the full finite
heat-bath sweep operator `Q = ∏_t Q_t`. -/
theorem finiteVolumeAssignmentPMF_finiteRegionHeatBathSweepPMF_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom) :
    let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
    let hZΔ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M' Δ ξ
    M.finiteRegionHeatBathSweepPMF ξ
      (finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ) =
      finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let hZΔ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M' Δ ξ
  let pΔ := finiteVolumeAssignmentPMF M'.toInfiniteGroundMLNSpec Δ ξ hZΔ
  unfold finiteRegionHeatBathSweepPMF
  have hfix :
      ∀ i : RegionAtom Atom Δ,
        M.singleSiteHeatBathUpdatePMF i ξ pΔ = pΔ := by
    intro i
    simpa [pΔ] using
      (M.finiteVolumeAssignmentPMF_singleSiteHeatBathUpdatePMF_eq (i := i) (ξ := ξ))
  simpa [pΔ, hfix] using
    show (Δ.attach.toList).foldl (fun q i => M.singleSiteHeatBathUpdatePMF i ξ q) pΔ = pΔ by
      induction Δ.attach.toList generalizing pΔ with
      | nil =>
          rfl
      | cons i is ih =>
          simp [List.foldl, hfix i]
          exact ih hfix

/-- Coupling-level lift of the finite heat-bath sweep operator. -/
noncomputable def finiteRegionHeatBathSweepCouplingPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ) :=
  (Δ.attach.toList).foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q

theorem finiteRegionHeatBathSweepCouplingPMF_map_fst
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.finiteRegionHeatBathSweepCouplingPMF ξ q).map Prod.fst =
      M.finiteRegionHeatBathSweepPMF ξ (q.map Prod.fst) := by
  unfold finiteRegionHeatBathSweepCouplingPMF finiteRegionHeatBathSweepPMF
  induction Δ.attach.toList generalizing q with
  | nil =>
      rfl
  | cons i is ih =>
      simp [List.foldl]
      rw [ih (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q)]
      rw [M.singleSiteHeatBathUpdateCouplingPMF_map_fst]

theorem finiteRegionHeatBathSweepCouplingPMF_map_snd
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.finiteRegionHeatBathSweepCouplingPMF ξ q).map Prod.snd =
      M.finiteRegionHeatBathSweepPMF ξ (q.map Prod.snd) := by
  unfold finiteRegionHeatBathSweepCouplingPMF finiteRegionHeatBathSweepPMF
  induction Δ.attach.toList generalizing q with
  | nil =>
      rfl
  | cons i is ih =>
      simp [List.foldl]
      rw [ih (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q)]
      rw [M.singleSiteHeatBathUpdateCouplingPMF_map_snd]

theorem finiteRegionCouplingExpectedDisagreement_foldl_singleSiteHeatBathUpdateCoupling_control
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    {l : List (RegionAtom Atom Δ)}
    (hNodup : l.Nodup)
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (s : ℝ)
    (hs_nonneg : 0 ≤ s)
    (hs : ∀ a ∈ Δ,
      finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a ≤ s)
    (hconst_le_one : M.finiteRegionPairwiseDobrushinConstant Δ ≤ 1) :
    (∀ a ∈ Δ,
      finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (l.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q) a ≤ s) ∧
    (∀ a : RegionAtom Atom Δ, a ∈ l →
      finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (l.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q) a.1 ≤
          M.finiteRegionPairwiseDobrushinConstant Δ * s) ∧
    (∀ a : RegionAtom Atom Δ, a ∉ l →
      finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (l.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q) a.1 =
          finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a.1) := by
  induction l generalizing q with
  | nil =>
      constructor
      · simpa using hs
      constructor
      · intro a ha
        cases ha
      · intro a ha
        simp
  | cons i is ih =>
      rcases List.nodup_cons.mp hNodup with ⟨hi_notin, his_nodup⟩
      let q₁ := M.singleSiteHeatBathUpdateCouplingPMF i ξ q
      have hconst_nonneg : 0 ≤ M.finiteRegionPairwiseDobrushinConstant Δ :=
        M.finiteRegionPairwiseDobrushinConstant_nonneg Δ
      have hsupq_le_s :
          finiteRegionSupSeminorm Δ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ≤ s := by
        exact finiteRegionSupSeminorm_le_of_bound hs_nonneg hs
      have hq₁_bound :
          ∀ a ∈ Δ,
            finiteRegionCouplingExpectedDisagreement (Atom := Atom) q₁ a ≤ s := by
        intro a ha
        by_cases hai : a = i.1
        · subst hai
          have hrow_le :
              Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient i.1 b) ≤
                M.finiteRegionPairwiseDobrushinConstant Δ := by
            exact le_finiteRegionSupSeminorm
              (Λ := Δ)
              (d := fun a => Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b))
              i.2
          have hpair_le :
              M.pairwiseDobrushinOperator Δ
                  (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) i.1 ≤
                M.finiteRegionPairwiseDobrushinConstant Δ * s := by
            calc
              M.pairwiseDobrushinOperator Δ
                  (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) i.1
                ≤ Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient i.1 b) *
                    finiteRegionSupSeminorm Δ
                      (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
                    exact M.pairwiseDobrushinOperator_le_rowSum_mul_finiteRegionSupSeminorm i.1
              _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ *
                  finiteRegionSupSeminorm Δ
                    (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
                    exact mul_le_mul_of_nonneg_right hrow_le
                      (finiteRegionSupSeminorm_nonneg (fun b hb =>
                        finiteRegionCouplingExpectedDisagreement_nonneg (Atom := Atom) q b))
              _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ * s := by
                    exact mul_le_mul_of_nonneg_left hsupq_le_s hconst_nonneg
          have hmul_le_s :
              M.finiteRegionPairwiseDobrushinConstant Δ * s ≤ s := by
            nlinarith
          exact le_trans
            (M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_le_pairwiseDobrushinOperator
              i ξ q)
            (le_trans hpair_le hmul_le_s)
        · have hneq : a ≠ i.1 := hai
          simpa [q₁] using
            (M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_eq_of_ne
              i ⟨a, ha⟩ hneq ξ q).le.trans (hs a ha)
      have hIH := ih his_nodup q₁ hq₁_bound
      rcases hIH with ⟨hbound_tail, hupdated_tail, hunchanged_tail⟩
      constructor
      · simpa [List.foldl_cons, q₁] using hbound_tail
      constructor
      · intro a ha_mem
        rw [List.mem_cons] at ha_mem
        rcases ha_mem with ha_eq | ha_mem
        · subst ha_eq
          have hi_eq :
              finiteRegionCouplingExpectedDisagreement (Atom := Atom)
                  (is.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q₁) a.1 =
                finiteRegionCouplingExpectedDisagreement (Atom := Atom) q₁ a.1 := by
            exact hunchanged_tail a hi_notin
          rw [List.foldl_cons, hi_eq]
          have hrow_le :
              Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a.1 b) ≤
                M.finiteRegionPairwiseDobrushinConstant Δ := by
            exact le_finiteRegionSupSeminorm
              (Λ := Δ)
              (d := fun a => Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b))
              a.2
          have hpair_le :
              M.pairwiseDobrushinOperator Δ
                  (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) a.1 ≤
                M.finiteRegionPairwiseDobrushinConstant Δ * s := by
            calc
              M.pairwiseDobrushinOperator Δ
                  (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) a.1
                ≤ Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a.1 b) *
                    finiteRegionSupSeminorm Δ
                      (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
                    exact M.pairwiseDobrushinOperator_le_rowSum_mul_finiteRegionSupSeminorm a.1
              _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ *
                  finiteRegionSupSeminorm Δ
                    (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
                    exact mul_le_mul_of_nonneg_right hrow_le
                      (finiteRegionSupSeminorm_nonneg (fun b hb =>
                        finiteRegionCouplingExpectedDisagreement_nonneg (Atom := Atom) q b))
              _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ * s := by
                    exact mul_le_mul_of_nonneg_left hsupq_le_s hconst_nonneg
          exact le_trans
            (by
              simpa [q₁] using
                M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_le_pairwiseDobrushinOperator
                  a ξ q)
            hpair_le
        · simpa [List.foldl_cons, q₁] using hupdated_tail a ha_mem
      · intro a ha_notmem
        simp [List.mem_cons] at ha_notmem
        rcases ha_notmem with ⟨ha_ne_i, ha_notmem⟩
        have hneq : a.1 ≠ i.1 := by
          intro h
          apply ha_ne_i
          apply Subtype.ext
          exact h
        calc
          finiteRegionCouplingExpectedDisagreement (Atom := Atom)
              ((i :: is).foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q) a.1
            =
              finiteRegionCouplingExpectedDisagreement (Atom := Atom)
                (is.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q₁) a.1 := by
                  simp [List.foldl_cons, q₁]
          _ =
              finiteRegionCouplingExpectedDisagreement (Atom := Atom) q₁ a.1 := by
                exact hunchanged_tail a ha_notmem
          _ =
              finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a.1 := by
                simpa [q₁] using
                  (M.finiteRegionCouplingExpectedDisagreement_singleSiteHeatBathUpdateCoupling_eq_of_ne
                    i a hneq ξ q)

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_finiteRegionHeatBathSweepCoupling_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ
        (finiteRegionCouplingExpectedDisagreement (Atom := Atom)
          (M.finiteRegionHeatBathSweepCouplingPMF ξ q)) ≤
      M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ
          (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
  let s :=
    finiteRegionSupSeminorm Δ
      (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q)
  have hs_nonneg : 0 ≤ s := by
    exact finiteRegionSupSeminorm_nonneg (fun a ha =>
      finiteRegionCouplingExpectedDisagreement_nonneg (Atom := Atom) q a)
  have hs :
      ∀ a ∈ Δ,
        finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a ≤ s := by
    intro a ha
    exact le_finiteRegionSupSeminorm
      (Λ := Δ)
      (d := finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ha
  have hconst_lt : M.finiteRegionPairwiseDobrushinConstant Δ < 1 :=
    M.finiteRegionPairwiseDobrushinConstant_lt_one hM Δ
  have hconst_le_one : M.finiteRegionPairwiseDobrushinConstant Δ ≤ 1 :=
    le_of_lt hconst_lt
  have hNodup : Δ.attach.toList.Nodup := by
    simpa using Δ.attach.nodup_toList
  have hcontrol :=
    finiteRegionCouplingExpectedDisagreement_foldl_singleSiteHeatBathUpdateCoupling_control
      (M := M) (l := Δ.attach.toList) hNodup ξ q s hs_nonneg hs hconst_le_one
  rcases hcontrol with ⟨_, hupdated, _⟩
  refine finiteRegionSupSeminorm_le_of_bound
    (c := M.finiteRegionPairwiseDobrushinConstant Δ * s)
    (mul_nonneg (M.finiteRegionPairwiseDobrushinConstant_nonneg Δ) hs_nonneg) ?_
  intro a ha
  have ha_mem : (⟨a, ha⟩ : RegionAtom Atom Δ) ∈ Δ.attach.toList := by
    simp
  simpa [finiteRegionHeatBathSweepCouplingPMF, s] using hupdated ⟨a, ha⟩ ha_mem

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_finiteRegionHeatBathSweepCoupling_lt
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperSmallTotalInfluence)
    {Δ : Region Atom}
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hq_pos :
      0 <
        finiteRegionSupSeminorm Δ
          (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q)) :
    finiteRegionSupSeminorm Δ
        (finiteRegionCouplingExpectedDisagreement (Atom := Atom)
          (M.finiteRegionHeatBathSweepCouplingPMF ξ q)) <
      finiteRegionSupSeminorm Δ
        (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
  let d := finiteRegionCouplingExpectedDisagreement (Atom := Atom) q
  have hd_nonneg : ∀ a ∈ Δ, 0 ≤ d a := by
    intro a ha
    exact finiteRegionCouplingExpectedDisagreement_nonneg (Atom := Atom) q a
  refine lt_of_le_of_lt
    (M.finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_finiteRegionHeatBathSweepCoupling_le
      hM ξ q)
    ?_
  simpa [d] using
    (show M.finiteRegionPairwiseDobrushinConstant Δ *
        finiteRegionSupSeminorm Δ d <
      finiteRegionSupSeminorm Δ d from by
        have hconst_lt : M.finiteRegionPairwiseDobrushinConstant Δ < 1 :=
          M.finiteRegionPairwiseDobrushinConstant_lt_one hM Δ
        nlinarith)

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

/-- Probability that a finite coupling places unequal local assignments on the two sides. -/
noncomputable def finiteRegionCouplingAssignmentDisagreementProbability
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) : ℝ :=
  ∑ z, (if z.1 = z.2 then 0 else 1) * ENNReal.toReal (q z)

/-- Expected Hamming disagreement of a finite coupling of local assignments. -/
noncomputable def finiteRegionCouplingExpectedHammingDisagreement
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) : ℝ :=
  ∑ z, (Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a)) * ENNReal.toReal (q z)

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

theorem finiteRegionCouplingAssignmentDisagreementProbability_nonneg
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    0 ≤ finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  unfold finiteRegionCouplingAssignmentDisagreementProbability
  exact Finset.sum_nonneg fun z hz => by
    by_cases h : z.1 = z.2
    · simp [h]
    · simp [h, ENNReal.toReal_nonneg]

theorem finiteRegionCouplingExpectedHammingDisagreement_nonneg
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    0 ≤ finiteRegionCouplingExpectedHammingDisagreement (Atom := Atom) q := by
  unfold finiteRegionCouplingExpectedHammingDisagreement
  exact Finset.sum_nonneg fun z hz =>
    mul_nonneg
      (Finset.sum_nonneg fun a ha => disagreementIndicator_nonneg z.1 z.2 a)
      ENNReal.toReal_nonneg

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

theorem sum_singletonEventIndicator_abs_eq_two_if_ne
    {Δ : Region Atom}
    (x y : LocalAssignment Atom Δ) :
    ∑ z : LocalAssignment Atom Δ,
      |finiteRegionEventIndicator (Atom := Atom) ({z} : Set (LocalAssignment Atom Δ)) x -
        finiteRegionEventIndicator (Atom := Atom) ({z} : Set (LocalAssignment Atom Δ)) y| =
      if x = y then 0 else 2 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    simp [finiteRegionEventIndicator]
  · let term : LocalAssignment Atom Δ → ℝ := fun z =>
      |finiteRegionEventIndicator (Atom := Atom) ({z} : Set (LocalAssignment Atom Δ)) x -
        finiteRegionEventIndicator (Atom := Atom) ({z} : Set (LocalAssignment Atom Δ)) y|
    have hx : x ∈ (Finset.univ : Finset (LocalAssignment Atom Δ)) := by simp
    have hy : y ∈ (Finset.univ.erase x : Finset (LocalAssignment Atom Δ)) := by
      exact Finset.mem_erase.mpr ⟨by simpa [eq_comm] using hxy, by simp⟩
    have hsplit_x :
        ∑ z : LocalAssignment Atom Δ, term z =
          term x + Finset.sum (Finset.univ.erase x) term := by
      simpa only [add_comm] using
        (Finset.sum_erase_add (s := Finset.univ) (f := term) (a := x) hx).symm
    have hsplit_y :
        Finset.sum (Finset.univ.erase x) term =
          term y + Finset.sum ((Finset.univ.erase x).erase y) term := by
      simpa [add_comm] using
        (Finset.sum_erase_add (s := Finset.univ.erase x) (f := term) (a := y) hy).symm
    have hrest :
        Finset.sum ((Finset.univ.erase x).erase y) term = 0 := by
      refine Finset.sum_eq_zero ?_
      intro z hz
      have hz_ne_y : z ≠ y := (Finset.mem_erase.mp hz).1
      have hz_mem : z ∈ Finset.univ.erase x := (Finset.mem_erase.mp hz).2
      have hz_ne_x : z ≠ x := (Finset.mem_erase.mp hz_mem).1
      have hxnz : x ≠ z := by
        intro hxz
        exact hz_ne_x hxz.symm
      have hynz : y ≠ z := by
        intro hyz
        exact hz_ne_y hyz.symm
      simp [finiteRegionEventIndicator, hxnz, hynz]
    calc
      ∑ z : LocalAssignment Atom Δ, term z
        = term x + Finset.sum (Finset.univ.erase x) term := hsplit_x
      _ = 1 + Finset.sum (Finset.univ.erase x) term := by
            have hyx : y ≠ x := by
              intro hyx
              exact hxy hyx.symm
            simp [term, finiteRegionEventIndicator, hyx]
      _ = 1 + (term y + Finset.sum ((Finset.univ.erase x).erase y) term) := by
            simp [hsplit_y]
      _ = 1 + (1 + Finset.sum ((Finset.univ.erase x).erase y) term) := by
            simp [term, finiteRegionEventIndicator, hxy]
      _ = 2 := by
            norm_num [hrest]
      _ = if x = y then 0 else 2 := by
            simp [hxy]

theorem sum_finiteRegionCouplingExpectedEventDisagreement_singleton_eq_two_mul_assignmentDisagreementProbability
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    ∑ x : LocalAssignment Atom Δ,
      finiteRegionCouplingExpectedEventDisagreement (Atom := Atom) q ({x} : Set (LocalAssignment Atom Δ)) =
      2 * finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  unfold finiteRegionCouplingExpectedEventDisagreement
    finiteRegionCouplingAssignmentDisagreementProbability
  calc
    ∑ x : LocalAssignment Atom Δ,
        ∑ z, |finiteRegionEventIndicator (Atom := Atom) ({x} : Set (LocalAssignment Atom Δ)) z.1 -
          finiteRegionEventIndicator (Atom := Atom) ({x} : Set (LocalAssignment Atom Δ)) z.2| *
            ENNReal.toReal (q z)
      = ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          (∑ x : LocalAssignment Atom Δ,
            |finiteRegionEventIndicator (Atom := Atom) ({x} : Set (LocalAssignment Atom Δ)) z.1 -
              finiteRegionEventIndicator (Atom := Atom) ({x} : Set (LocalAssignment Atom Δ)) z.2|) *
            ENNReal.toReal (q z) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro z hz
              rw [Finset.sum_mul]
    _ = ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          (if z.1 = z.2 then 0 else 2) * ENNReal.toReal (q z) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [sum_singletonEventIndicator_abs_eq_two_if_ne (Atom := Atom) z.1 z.2]
    _ = 2 * finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
          calc
            ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
                (if z.1 = z.2 then 0 else 2) * ENNReal.toReal (q z)
              = ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
                  2 * ((if z.1 = z.2 then 0 else 1) * ENNReal.toReal (q z)) := by
                    refine Finset.sum_congr rfl ?_
                    intro z hz
                    by_cases h : z.1 = z.2 <;> simp [h]
            _ = 2 * ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
                  (if z.1 = z.2 then 0 else 1) * ENNReal.toReal (q z) := by
                    rw [Finset.mul_sum]
            _ = 2 * finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
                    simp [finiteRegionCouplingAssignmentDisagreementProbability]

theorem finiteRegionAssignmentL1Discrepancy_le_two_mul_couplingAssignmentDisagreementProbability
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) :
    M.finiteRegionAssignmentL1Discrepancy μ ν Δ ≤
      2 * finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  unfold finiteRegionAssignmentL1Discrepancy
  calc
    ∑ x : LocalAssignment Atom Δ, M.finiteRegionAssignmentProbabilityDiscrepancy μ ν Δ x
      ≤ ∑ x : LocalAssignment Atom Δ,
          finiteRegionCouplingExpectedEventDisagreement (Atom := Atom) q ({x} : Set (LocalAssignment Atom Δ)) := by
            refine Finset.sum_le_sum ?_
            intro x hx
            exact M.finiteRegionSetProbabilityDiscrepancy_le_of_limitMarginalCoupling
              μ ν Δ ({x} : Set (LocalAssignment Atom Δ)) q hqfst hqsnd
    _ = 2 * finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
          exact sum_finiteRegionCouplingExpectedEventDisagreement_singleton_eq_two_mul_assignmentDisagreementProbability
            (Atom := Atom) q

theorem finiteRegionAssignmentTotalVariation_le_couplingAssignmentDisagreementProbability
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) :
    M.finiteRegionAssignmentTotalVariation μ ν Δ ≤
      finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  unfold finiteRegionAssignmentTotalVariation
  have hmain :=
    M.finiteRegionAssignmentL1Discrepancy_le_two_mul_couplingAssignmentDisagreementProbability
      μ ν Δ q hqfst hqsnd
  nlinarith [finiteRegionCouplingAssignmentDisagreementProbability_nonneg (Atom := Atom) q]

theorem finiteRegionCouplingExpectedHammingDisagreement_eq_sum_expectedDisagreement
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedHammingDisagreement (Atom := Atom) q =
      Finset.sum Δ (fun a => finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a) := by
  unfold finiteRegionCouplingExpectedHammingDisagreement finiteRegionCouplingExpectedDisagreement
  calc
    ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
        (Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a)) * ENNReal.toReal (q z)
      = ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a * ENNReal.toReal (q z)) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [Finset.sum_mul]
    _ = Finset.sum Δ (fun a => ∑ z : LocalAssignment Atom Δ × LocalAssignment Atom Δ,
          disagreementIndicator z.1 z.2 a * ENNReal.toReal (q z)) := by
            rw [Finset.sum_comm]
    _ = Finset.sum Δ (fun a => finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a) := by
            rfl

theorem finiteRegionCouplingAssignmentDisagreementProbability_le_expectedHamming
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q ≤
      finiteRegionCouplingExpectedHammingDisagreement (Atom := Atom) q := by
  unfold finiteRegionCouplingAssignmentDisagreementProbability finiteRegionCouplingExpectedHammingDisagreement
  refine Finset.sum_le_sum ?_
  intro z hz
  by_cases hxy : z.1 = z.2
  · have hsum0 : Finset.sum Δ (fun a => disagreementIndicator z.2 z.2 a) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro a ha
      have hnotmem : a ∉ disagreementRegion z.2 z.2 := by
        intro hmem
        rcases (mem_disagreementRegion_iff z.2 z.2).1 hmem with ⟨_, hneq⟩
        exact hneq rfl
      simp [disagreementIndicator, hnotmem]
    simp [hxy, hsum0]
  · have hone :
        (1 : ℝ) ≤ Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a) := by
        have hnotall : ¬ ∀ i : Δ, z.1 i = z.2 i := by
          intro hall
          apply hxy
          ext i
          exact hall i
        rcases Classical.not_forall.mp hnotall with ⟨i, hi⟩
        have hmem : i.1 ∈ disagreementRegion z.1 z.2 := by
          exact (mem_disagreementRegion_iff z.1 z.2).2 ⟨i.2, hi⟩
        have hval : disagreementIndicator z.1 z.2 i.1 = 1 := by
          simp [disagreementIndicator, hmem]
        calc
          (1 : ℝ) = disagreementIndicator z.1 z.2 i.1 := by simp [hval]
          _ ≤ Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a) := by
              exact Finset.single_le_sum
                (fun a ha => disagreementIndicator_nonneg z.1 z.2 a) i.2
    have hqnonneg : 0 ≤ ENNReal.toReal (q z) := ENNReal.toReal_nonneg
    have hmul :
        1 * ENNReal.toReal (q z) ≤
          (Finset.sum Δ (fun a => disagreementIndicator z.1 z.2 a)) * ENNReal.toReal (q z) :=
      mul_le_mul_of_nonneg_right hone hqnonneg
    simpa [hxy] using hmul

theorem finiteRegionCouplingExpectedDisagreement_le_assignmentDisagreementProbability
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a ≤
      finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  unfold finiteRegionCouplingExpectedDisagreement
    finiteRegionCouplingAssignmentDisagreementProbability
  refine Finset.sum_le_sum ?_
  intro z hz
  by_cases hxy : z.1 = z.2
  · have hnot : a ∉ disagreementRegion z.2 z.2 := by
      intro hmem
      rcases (mem_disagreementRegion_iff z.2 z.2).1 hmem with ⟨_, hneq⟩
      exact hneq rfl
    simp [hxy, disagreementIndicator, hnot]
  · have hbound : disagreementIndicator z.1 z.2 a ≤ 1 := by
      by_cases ha : a ∈ disagreementRegion z.1 z.2
      · simp [disagreementIndicator, ha]
      · simp [disagreementIndicator, ha]
    have hqnonneg : 0 ≤ ENNReal.toReal (q z) := ENNReal.toReal_nonneg
    have hmul :
        disagreementIndicator z.1 z.2 a * ENNReal.toReal (q z) ≤
          1 * ENNReal.toReal (q z) :=
      mul_le_mul_of_nonneg_right hbound hqnonneg
    simpa [hxy] using hmul

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_le_assignmentDisagreementProbability
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ≤
      finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q := by
  refine finiteRegionSupSeminorm_le_of_bound
    (c := finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) q)
    (finiteRegionCouplingAssignmentDisagreementProbability_nonneg (Atom := Atom) q) ?_
  intro a ha
  exact finiteRegionCouplingExpectedDisagreement_le_assignmentDisagreementProbability
    (Atom := Atom) q a

theorem finiteRegionCouplingExpectedHammingDisagreement_le_card_mul_sup
    {Δ : Region Atom}
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    finiteRegionCouplingExpectedHammingDisagreement (Atom := Atom) q ≤
      (Δ.card : ℝ) *
        finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
  rw [finiteRegionCouplingExpectedHammingDisagreement_eq_sum_expectedDisagreement (Atom := Atom) q]
  calc
    Finset.sum Δ (fun a => finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a)
      ≤ Finset.sum Δ
          (fun _ => finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q)) := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact le_finiteRegionSupSeminorm
              (Λ := Δ)
              (d := finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ha
    _ = (Δ.card : ℝ) *
        finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
            simp [Finset.sum_const, nsmul_eq_mul]

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

theorem finiteRegionAssignmentTotalVariation_eq_pmfTotalVariation
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom) :
    M.finiteRegionAssignmentTotalVariation μ ν Δ =
      pmfTotalVariation
        ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
        ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) := by
  unfold finiteRegionAssignmentTotalVariation pmfTotalVariation
    finiteRegionAssignmentL1Discrepancy pmfL1Discrepancy
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl ?_
  intro x hx
  exact M.finiteRegionAssignmentProbabilityDiscrepancy_eq_abs_sub_limitMarginalToReal μ ν Δ x

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

theorem finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF) :
    M.finiteRegionAssignmentTotalVariation μ ν Δ ≤
      (Δ.card : ℝ) *
        finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
  refine le_trans
    (M.finiteRegionAssignmentTotalVariation_le_couplingAssignmentDisagreementProbability
      μ ν Δ q hqfst hqsnd)
    (le_trans
      (finiteRegionCouplingAssignmentDisagreementProbability_le_expectedHamming
        (Atom := Atom) q)
      (finiteRegionCouplingExpectedHammingDisagreement_le_card_mul_sup
        (Atom := Atom) q))

theorem finiteRegionAssignmentTotalVariation_eq_zero_of_limitMarginalCoupling_sup_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (hqfst :
      q.map Prod.fst =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hqsnd :
      q.map Prod.snd =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF)
    (hsup :
      finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) = 0) :
    M.finiteRegionAssignmentTotalVariation μ ν Δ = 0 := by
  have hnonneg := M.finiteRegionAssignmentTotalVariation_nonneg μ ν Δ
  have hle :
      M.finiteRegionAssignmentTotalVariation μ ν Δ ≤ 0 := by
    calc
      M.finiteRegionAssignmentTotalVariation μ ν Δ
        ≤ (Δ.card : ℝ) *
            finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
              exact M.finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
                μ ν Δ q hqfst hqsnd
      _ = 0 := by simp [hsup]
  exact le_antisymm hle hnonneg

theorem eq_of_forall_exists_limitMarginalCoupling_sup_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hzero :
      ∀ Δ : Region Atom,
        ∃ q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ),
          q.map Prod.fst =
              (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
            q.map Prod.snd =
              (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (ν : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
            finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) = 0) :
    (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  apply M.eq_of_finiteRegionAssignmentTotalVariation_eq_zero μ ν
  intro Δ
  rcases hzero Δ with ⟨q, hqfst, hqsnd, hsup⟩
  exact M.finiteRegionAssignmentTotalVariation_eq_zero_of_limitMarginalCoupling_sup_eq_zero
    μ ν Δ q hqfst hqsnd hsup

theorem finiteRegionCouplingExpectedDisagreement_diagCoupling_eq_zero
    {Δ : Region Atom}
    (p : PMF (LocalAssignment Atom Δ))
    (a : Atom) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom) (diagCoupling p) a = 0 := by
  unfold finiteRegionCouplingExpectedDisagreement diagCoupling
  rw [sum_mul_toReal_map_eq (p := p) (h := fun x : LocalAssignment Atom Δ => (x, x))
    (f := fun z : LocalAssignment Atom Δ × LocalAssignment Atom Δ =>
      disagreementIndicator z.1 z.2 a)]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hnot : a ∉ disagreementRegion x x := by
    intro hmem
    rcases (mem_disagreementRegion_iff x x).1 hmem with ⟨_, hneq⟩
    exact hneq rfl
  simp [disagreementIndicator, hnot]

theorem finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_diagCoupling_eq_zero
    {Δ : Region Atom}
    (p : PMF (LocalAssignment Atom Δ)) :
    finiteRegionSupSeminorm Δ
        (finiteRegionCouplingExpectedDisagreement (Atom := Atom) (diagCoupling p)) = 0 := by
  apply finiteRegionSupSeminorm_eq_zero_of_eq_zero
  intro a ha
  exact finiteRegionCouplingExpectedDisagreement_diagCoupling_eq_zero (Atom := Atom) p a

/-- Abstract final bridge hypothesis: every finite-region boundary marginal pair admits
a coupling whose expected sitewise disagreement has zero sup seminorm. -/
def HasZeroSupLimitMarginalCouplings
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom)) : Prop :=
  ∀ Δ : Region Atom,
    ∃ q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ),
      q.map Prod.fst =
          (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
        q.map Prod.snd =
          (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
        finiteRegionSupSeminorm Δ (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) = 0

theorem eq_of_hasZeroSupLimitMarginalCouplings
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hzero : HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν) :
    (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  exact M.eq_of_forall_exists_limitMarginalCoupling_sup_eq_zero μ ν hzero

theorem hasZeroSupLimitMarginalCouplings_of_eq
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (hμν : (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom))) :
    HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν := by
  intro Δ
  let p : PMF (LocalAssignment Atom Δ) :=
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ).toPMF
  have hlim :
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ =
          Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν : Measure (InfiniteWorld Atom)) Δ := by
    simpa using congrArg
      (fun ρ : Measure (InfiniteWorld Atom) =>
        Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal ρ Δ)
      hμν
  have hpmf :
      p =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Δ).toPMF := by
    unfold p
    ext x
    simpa [MeasureTheory.Measure.toPMF_apply] using congrArg (fun ρ =>
          ρ {x}) hlim
  refine ⟨diagCoupling p, ?_, ?_, ?_⟩
  · change PMF.map Prod.fst (diagCoupling p) = p
    exact diagCoupling_map_fst (p := p)
  · change PMF.map Prod.snd (diagCoupling p) =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν : Measure (InfiniteWorld Atom)) Δ).toPMF
    rw [diagCoupling_map_snd (p := p)]
    exact hpmf
  · change finiteRegionSupSeminorm Δ
      (finiteRegionCouplingExpectedDisagreement (Atom := Atom) (diagCoupling p)) = 0
    exact
      finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_diagCoupling_eq_zero
        (Atom := Atom) p

theorem hasZeroSupLimitMarginalCouplings_iff_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom)) :
    HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν ↔
      (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom)) := by
  constructor
  · exact M.eq_of_hasZeroSupLimitMarginalCouplings μ ν
  · exact hasZeroSupLimitMarginalCouplings_of_eq (Atom := Atom) μ ν

theorem hasZeroSupLimitMarginalCouplings_of_finiteRegionAssignmentTotalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (htv : ∀ Δ : Region Atom, M.finiteRegionAssignmentTotalVariation μ ν Δ = 0) :
    HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν := by
  intro Δ
  let p : PMF (LocalAssignment Atom Δ) :=
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ).toPMF
  let q : PMF (LocalAssignment Atom Δ) :=
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (ν : Measure (InfiniteWorld Atom)) Δ).toPMF
  have htv_pmf : pmfTotalVariation p q = 0 := by
    unfold p q
    simpa using M.finiteRegionAssignmentTotalVariation_eq_pmfTotalVariation μ ν Δ ▸ htv Δ
  have hpq : p = q := pmf_eq_of_totalVariation_eq_zero p q htv_pmf
  refine ⟨diagCoupling p, ?_, ?_, ?_⟩
  · change PMF.map Prod.fst (diagCoupling p) = p
    exact diagCoupling_map_fst (p := p)
  · change PMF.map Prod.snd (diagCoupling p) = q
    rw [diagCoupling_map_snd (p := p), hpq]
  · exact
      finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_diagCoupling_eq_zero
        (Atom := Atom) p

theorem finiteRegionAssignmentTotalVariation_eq_zero_of_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    (Δ : Region Atom)
    (hμν : (μ : Measure (InfiniteWorld Atom)) = (ν : Measure (InfiniteWorld Atom))) :
    M.finiteRegionAssignmentTotalVariation μ ν Δ = 0 := by
  let p : PMF (LocalAssignment Atom Δ) :=
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (μ : Measure (InfiniteWorld Atom)) Δ).toPMF
  let q : PMF (LocalAssignment Atom Δ) :=
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (ν : Measure (InfiniteWorld Atom)) Δ).toPMF
  have hlim :
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ =
          Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν : Measure (InfiniteWorld Atom)) Δ := by
    simpa using congrArg
      (fun ρ : Measure (InfiniteWorld Atom) =>
        Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal ρ Δ)
      hμν
  have hpq : p = q := by
    unfold p q
    ext x
    simpa [MeasureTheory.Measure.toPMF_apply] using congrArg (fun ρ =>
      ρ {x}) hlim
  calc
    M.finiteRegionAssignmentTotalVariation μ ν Δ = pmfTotalVariation p q := by
      unfold p q
      exact M.finiteRegionAssignmentTotalVariation_eq_pmfTotalVariation μ ν Δ
    _ = 0 := by
      rw [hpq, pmfTotalVariation_self]

theorem hasZeroSupLimitMarginalCouplings_iff_finiteRegionAssignmentTotalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom)) :
    HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν ↔
      ∀ Δ : Region Atom, M.finiteRegionAssignmentTotalVariation μ ν Δ = 0 := by
  constructor
  · intro hzero Δ
    exact M.finiteRegionAssignmentTotalVariation_eq_zero_of_eq μ ν Δ
      (M.eq_of_hasZeroSupLimitMarginalCouplings μ ν hzero)
  · exact M.hasZeroSupLimitMarginalCouplings_of_finiteRegionAssignmentTotalVariation_eq_zero μ ν

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

theorem paperUniqueMeasure_of_hasZeroSupLimitMarginalCouplings
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hzero :
      ∀ (μ ν : ProbabilityMeasure (InfiniteWorld Atom)),
        FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ : Measure (InfiniteWorld Atom)) →
          FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
            (ν : Measure (InfiniteWorld Atom)) →
            HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν) :
    M.PaperUniqueMeasure := by
  intro μ ν hμ hν
  exact M.eq_of_hasZeroSupLimitMarginalCouplings μ ν (hzero μ ν hμ hν)

theorem paperUniqueMeasure_of_finiteRegionAssignmentTotalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hzero :
      ∀ (μ ν : ProbabilityMeasure (InfiniteWorld Atom)),
        FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ : Measure (InfiniteWorld Atom)) →
          FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
            (ν : Measure (InfiniteWorld Atom)) →
            ∀ Δ : Region Atom, M.finiteRegionAssignmentTotalVariation μ ν Δ = 0) :
    M.PaperUniqueMeasure := by
  apply M.paperUniqueMeasure_of_hasZeroSupLimitMarginalCouplings
  intro μ ν hμ hν
  exact M.hasZeroSupLimitMarginalCouplings_of_finiteRegionAssignmentTotalVariation_eq_zero
    μ ν (hzero μ ν hμ hν)

theorem paperUniqueMeasure_iff_hasZeroSupLimitMarginalCouplings
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    M.PaperUniqueMeasure ↔
      ∀ (μ ν : ProbabilityMeasure (InfiniteWorld Atom)),
        FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ : Measure (InfiniteWorld Atom)) →
          FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
            (ν : Measure (InfiniteWorld Atom)) →
            HasZeroSupLimitMarginalCouplings (Atom := Atom) μ ν := by
  constructor
  · intro h μ ν hμ hν
    exact hasZeroSupLimitMarginalCouplings_of_eq (Atom := Atom) μ ν (h μ ν hμ hν)
  · exact M.paperUniqueMeasure_of_hasZeroSupLimitMarginalCouplings

theorem paperUniqueMeasure_iff_finiteRegionAssignmentTotalVariation_eq_zero
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    M.PaperUniqueMeasure ↔
      ∀ (μ ν : ProbabilityMeasure (InfiniteWorld Atom)),
        FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ : Measure (InfiniteWorld Atom)) →
          FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
            (ν : Measure (InfiniteWorld Atom)) →
            ∀ Δ : Region Atom, M.finiteRegionAssignmentTotalVariation μ ν Δ = 0 := by
  constructor
  · intro h μ ν hμ hν Δ
    exact M.finiteRegionAssignmentTotalVariation_eq_zero_of_eq μ ν Δ (h μ ν hμ hν)
  · exact M.paperUniqueMeasure_of_finiteRegionAssignmentTotalVariation_eq_zero

/-- **Variational bound for weighted sums (Georgii Prop. 8.8, simplified).**

    For PMFs `p, q` on a finite type and a function `f` valued in `[0, C]`,
    the weighted sum difference is bounded by `C` times the L1 distance.

    This is weaker than the coordinate-wise Dobrushin bound but sufficient
    when combined with the coupling-based machinery that already handles
    the coordinate-wise structure. -/
theorem abs_weighted_sum_diff_le_sup_mul_l1
    {α : Type*} [Fintype α]
    (p q : PMF α) (f : α → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) :
    |∑ x, f x * (p x).toReal - ∑ x, f x * (q x).toReal| ≤
      C * pmfL1Discrepancy p q := by
  calc |∑ x, f x * (p x).toReal - ∑ x, f x * (q x).toReal|
      = |∑ x, f x * ((p x).toReal - (q x).toReal)| := by
        rw [← Finset.sum_sub_distrib]; congr 1
        refine Finset.sum_congr rfl ?_; intro x _; ring
    _ ≤ ∑ x, |f x * ((p x).toReal - (q x).toReal)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |f x| * |(p x).toReal - (q x).toReal| := by
        refine Finset.sum_congr rfl ?_; intro x _; exact abs_mul _ _
    _ ≤ ∑ x, C * |(p x).toReal - (q x).toReal| := by
        refine Finset.sum_le_sum ?_; intro x _
        exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
    _ = C * ∑ x, |(p x).toReal - (q x).toReal| := by rw [← Finset.mul_sum]
    _ = C * pmfL1Discrepancy p q := by rfl

/-- **DLR marginal fixed-point**: For a DLR measure `μ` and an interior site
    `i` (whose interaction neighborhood is contained in `Δ`), the `Δ`-marginal
    of `μ` is a fixed point of the single-site heat-bath update at `i`.

    The proof uses the `FixedRegionCylinderDLR` equation at region `{i}` with
    cylinder event on `Δ`, combined with the
    `limitMarginal_lintegral_cylinderBoundaryKernelValue` decomposition.

    Mathematically: for interior `i`, the DLR equation gives
    `μ_Δ(y) = γ_i(y_i | y_{∂i}) · μ_{Δ∖{i}}(y_{Δ∖{i}})`,
    which is precisely the fixed-point condition for the heat-bath update. -/
theorem limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hi_nbhd : M.atomInteractionNeighborhood i.1 ⊆ Δ) :
    M.singleSiteHeatBathUpdatePMF i ξ
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF := by
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let pμ := (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
    (μ : Measure (InfiniteWorld Atom)) Δ).toPMF
  ext y
  have hsingleton : MeasurableSet ({y} : Set (LocalAssignment Atom Δ)) :=
    MeasurableSet.singleton y
  -- The update formula: (update pμ)({y}) = Σ_b pμ(b) * worldMeasure({i})(patch b ξ)(cyl)
  have hupdate :=
    M.singleSiteHeatBathUpdatePMF_toMeasure_apply i ξ pμ ({y} : Set (LocalAssignment Atom Δ))
      hsingleton
  rw [tsum_fintype] at hupdate
  -- The DLR equation: ∫ worldMeasure({i})(ω)(cyl) dμ(ω) = μ(cyl)
  have hdlr :
      ∫⁻ ω,
        M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
        ∂ (μ : Measure (InfiniteWorld Atom)) =
        (μ : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) :=
    hμ ({i.1} : Region Atom) Δ ({y} : Set (LocalAssignment Atom Δ)) hsingleton
  -- Following GPT-5.4 Pro: direct lintegral_fintype → toPMF_toMeasure → lintegral_map
  --   → boundary independence → hdlr
  -- Both sides of the target equality equal μ(cylinder Δ {y}).
  --
  -- The sum Σ pμ(b) * worldMeasure(patch b ξ)(cyl) = pμ.toMeasure({y})
  have hdlr_sum :
      ∑ b, pμ b *
        (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) =
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) := by
    let f : LocalAssignment Atom Δ → ENNReal := fun b =>
      (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
        (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
    let J : Region Atom :=
      cylinderBoundarySupportRegion M'.toInfiniteGroundMLNSpec ({i.1} : Region Atom) Δ
    have hsum_as_lintegral :
        ∑ b, pμ b * f b = ∫⁻ b, f b ∂ pμ.toMeasure := by
      calc
        ∑ b, pμ b * f b
            = ∑ b, f b * pμ.toMeasure ({b} : Set (LocalAssignment Atom Δ)) := by
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
        _ = ∫⁻ b, f b ∂ pμ.toMeasure := by
                symm
                exact MeasureTheory.lintegral_fintype (μ := pμ.toMeasure) f
    have hboundaryEq :
        boundaryClauseSupportRegion M'.toInfiniteGroundMLNSpec ({i.1} : Region Atom) =
          M.atomInteractionNeighborhood i.1 := by
      simpa [M'] using
        M.boundaryClauseSupportRegion_singleton_eq_atomInteractionNeighborhood i.1
    have hJsubset : J ⊆ Δ := by
      intro a ha
      have ha' :
          a ∈ M.atomInteractionNeighborhood i.1 ∪ outsideRegion ({i.1} : Region Atom) Δ := by
        simpa [J, cylinderBoundarySupportRegion, hboundaryEq] using ha
      rcases Finset.mem_union.mp ha' with ha_nbhd | ha_out
      · exact hi_nbhd ha_nbhd
      · have ha_out' : a ∈ Δ \ ({i.1} : Region Atom) := by
          simpa [outsideRegion] using ha_out
        exact (Finset.mem_sdiff.mp ha_out').1
    have hrestrict_patch :
        ∀ ω : InfiniteWorld Atom,
          Finset.restrict J (patch Δ (Finset.restrict Δ ω) ξ) =
            Finset.restrict J ω := by
      intro ω
      funext a
      have haΔ : a.1 ∈ Δ := hJsubset a.2
      simp [J, patch, haΔ]
    have hboundary :
        ∀ ω : InfiniteWorld Atom,
          f (Finset.restrict Δ ω) =
            M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
              (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
      intro ω
      show f (Finset.restrict Δ ω) = _
      dsimp only [f]
      exact
        (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq'
            (M := M') (Λ := ({i.1} : Region Atom)) (I := Δ)
            (S := ({y} : Set (LocalAssignment Atom Δ))) hsingleton
            (ξ₁ := patch Δ (Finset.restrict Δ ω) ξ) (ξ₂ := ω)
            (by simpa [J] using hrestrict_patch ω))
    have hrhs :
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) =
          (μ : Measure (InfiniteWorld Atom))
            (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
      calc
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ))
            =
          (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) Δ)
            ({y} : Set (LocalAssignment Atom Δ)) := by
              simp [pμ, MeasureTheory.Measure.toPMF_toMeasure]
        _ =
          (μ : Measure (InfiniteWorld Atom))
            ((Finset.restrict Δ) ⁻¹' ({y} : Set (LocalAssignment Atom Δ))) := by
              rw [Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal]
              rw [MeasureTheory.Measure.map_apply (Finset.measurable_restrict Δ) hsingleton]
        _ =
          (μ : Measure (InfiniteWorld Atom))
            (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
              congr 1
    calc
      ∑ b, pμ b *
        (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
          = ∫⁻ b, f b ∂ pμ.toMeasure := by
              simpa [f] using hsum_as_lintegral
      _ =
        ∫⁻ b, f b
          ∂ (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ) := by
              simp [pμ, MeasureTheory.Measure.toPMF_toMeasure]
      _ =
        ∫⁻ ω, f (Finset.restrict Δ ω) ∂ (μ : Measure (InfiniteWorld Atom)) := by
              simpa [Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal] using
                (MeasureTheory.lintegral_map
                  (μ := (μ : Measure (InfiniteWorld Atom)))
                  (f := f)
                  (g := Finset.restrict Δ)
                  (Measurable.of_discrete)
                  (Finset.measurable_restrict Δ))
      _ =
        ∫⁻ ω,
          M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
            (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
          ∂ (μ : Measure (InfiniteWorld Atom)) := by
              exact MeasureTheory.lintegral_congr (fun ω => hboundary ω)
      _ =
        (μ : Measure (InfiniteWorld Atom))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := hdlr
      _ = pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) := hrhs.symm
  rw [hdlr_sum] at hupdate
  simpa [pμ, PMF.toMeasure_apply_singleton] using hupdate

-- ═══════════════════════════════════════════════════════════════════════════
-- Infrastructure for the descending-shell Dobrushin uniqueness proof
-- ═══════════════════════════════════════════════════════════════════════════

/-- Restrict a local assignment from a larger region to a subregion. -/
def restrictAssignment
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ)
    (x : LocalAssignment Atom Δ) : LocalAssignment Atom Γ :=
  fun ⟨a, ha⟩ => x ⟨a, hΓΔ ha⟩

omit [DecidableEq Atom] in
theorem limitMarginal_toPMF_map_restrictAssignment
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ) :
    (((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF).map (restrictAssignment hΓΔ)) =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Γ).toPMF := by
  have hproj :
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).map (restrictAssignment hΓΔ) =
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Γ) := by
    unfold Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
    change Measure.map
        (Finset.restrict₂
          (ι := Atom)
          (π := Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom)
          hΓΔ)
        (Measure.map (Finset.restrict Δ) (μ : Measure (InfiniteWorld Atom))) =
      Measure.map (Finset.restrict Γ) (μ : Measure (InfiniteWorld Atom))
    rw [Measure.map_map
      (Finset.measurable_restrict₂
        (X := Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom)
        hΓΔ)
      (Finset.measurable_restrict Δ)]
    congr 1
  ext x
  have hx : MeasurableSet ({x} : Set (LocalAssignment Atom Γ)) := MeasurableSet.singleton x
  have hprojx :
      ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).map (restrictAssignment hΓΔ))
        ({x} : Set (LocalAssignment Atom Γ)) =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Γ)
        ({x} : Set (LocalAssignment Atom Γ)) := by
    exact congrArg (fun ρ : Measure (LocalAssignment Atom Γ) => ρ ({x} : Set (LocalAssignment Atom Γ))) hproj
  calc
    ((((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF).map (restrictAssignment hΓΔ)) x)
      = ((((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (μ : Measure (InfiniteWorld Atom)) Δ).toPMF).map (restrictAssignment hΓΔ)).toMeasure
            ({x} : Set (LocalAssignment Atom Γ))) := by
              symm
              exact PMF.toMeasure_apply_singleton _ _ hx
    _ =
      ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).toPMF).toMeasure
        ((restrictAssignment hΓΔ) ⁻¹' ({x} : Set (LocalAssignment Atom Γ))) := by
          rw [PMF.toMeasure_map_apply
            (p := (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) Δ).toPMF)
            (f := restrictAssignment hΓΔ)
            (s := ({x} : Set (LocalAssignment Atom Γ)))
            (hf := Measurable.of_discrete)
            (hs := hx)]
    _ =
      ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Δ).map (restrictAssignment hΓΔ))
        ({x} : Set (LocalAssignment Atom Γ)) := by
          rw [Measure.map_apply (Measurable.of_discrete) hx]
          simp [MeasureTheory.Measure.toPMF_toMeasure]
    _ =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Γ) ({x} : Set (LocalAssignment Atom Γ)) := by
          exact hprojx
    _ =
      ((Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Γ).toPMF x) := by
          rw [MeasureTheory.Measure.toPMF_apply]

/-- Project a coupling on a larger region down to a subregion. -/
noncomputable def projectCouplingToSubregion
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Γ × LocalAssignment Atom Γ) :=
  q.map (fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))

omit [DecidableEq Atom] in
theorem projectCouplingToSubregion_map_fst
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (projectCouplingToSubregion hΓΔ q).map Prod.fst =
      (q.map Prod.fst).map (restrictAssignment hΓΔ) := by
  calc
    (projectCouplingToSubregion hΓΔ q).map Prod.fst
      = (q.map (fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))).map Prod.fst := by
          rfl
    _ = q.map (Prod.fst ∘ fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2)) := by
          simpa using
            (PMF.map_comp
              (p := q)
              (f := fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))
              Prod.fst)
    _ = q.map (restrictAssignment hΓΔ ∘ Prod.fst) := by
          rfl
    _ = (q.map Prod.fst).map (restrictAssignment hΓΔ) := by
          simpa using
            (PMF.map_comp
              (p := q)
              (f := Prod.fst)
              (restrictAssignment hΓΔ)).symm

omit [DecidableEq Atom] in
theorem projectCouplingToSubregion_map_snd
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (projectCouplingToSubregion hΓΔ q).map Prod.snd =
      (q.map Prod.snd).map (restrictAssignment hΓΔ) := by
  calc
    (projectCouplingToSubregion hΓΔ q).map Prod.snd
      = (q.map (fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))).map Prod.snd := by
          rfl
    _ = q.map (Prod.snd ∘ fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2)) := by
          simpa using
            (PMF.map_comp
              (p := q)
              (f := fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))
              Prod.snd)
    _ = q.map (restrictAssignment hΓΔ ∘ Prod.snd) := by
          rfl
    _ = (q.map Prod.snd).map (restrictAssignment hΓΔ) := by
          simpa using
            (PMF.map_comp
              (p := q)
              (f := Prod.snd)
              (restrictAssignment hΓΔ)).symm

/-- Disagreement at a site `a` is preserved by coupling projection, provided
    the disagreement indicator at `a` depends only on `z.1 a` and `z.2 a`
    (which are unchanged by `restrictAssignment`). -/
theorem finiteRegionCouplingExpectedDisagreement_projectCoupling_eq
    {Γ Δ : Region Atom}
    (hΓΔ : Γ ⊆ Δ)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ))
    (a : Atom) (ha : a ∈ Γ) :
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (projectCouplingToSubregion hΓΔ q) a =
      finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a := by
  let aΓ : RegionAtom Atom Γ := ⟨a, ha⟩
  have hmap :
      (projectCouplingToSubregion hΓΔ q).map (fun z => (z.1 aΓ, z.2 aΓ)) =
        q.map (fun z => (z.1 ⟨a, hΓΔ ha⟩, z.2 ⟨a, hΓΔ ha⟩)) := by
    calc
      (projectCouplingToSubregion hΓΔ q).map (fun z => (z.1 aΓ, z.2 aΓ))
        = (q.map (fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))).map
            (fun z => (z.1 aΓ, z.2 aΓ)) := by
              rfl
      _ = q.map
            ((fun z : LocalAssignment Atom Γ × LocalAssignment Atom Γ => (z.1 aΓ, z.2 aΓ)) ∘
              fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2)) := by
              simpa using
                (PMF.map_comp
                  (p := q)
                  (f := fun z => (restrictAssignment hΓΔ z.1, restrictAssignment hΓΔ z.2))
                  (fun z : LocalAssignment Atom Γ × LocalAssignment Atom Γ => (z.1 aΓ, z.2 aΓ)))
      _ = q.map (fun z => (z.1 ⟨a, hΓΔ ha⟩, z.2 ⟨a, hΓΔ ha⟩)) := by
            rfl
  calc
    finiteRegionCouplingExpectedDisagreement (Atom := Atom)
        (projectCouplingToSubregion hΓΔ q) a
      =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal
              (((projectCouplingToSubregion hΓΔ q).map
                (fun z => (z.1 aΓ, z.2 aΓ))) u) := by
            rw [finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair
              (q := projectCouplingToSubregion hΓΔ q) (a := aΓ)]
    _ =
        ∑ u : Bool × Bool,
          (if u.1 = u.2 then (0 : ℝ) else 1) *
            ENNReal.toReal
              ((q.map
                (fun z => (z.1 ⟨a, hΓΔ ha⟩, z.2 ⟨a, hΓΔ ha⟩))) u) := by
            rw [hmap]
    _ =
        finiteRegionCouplingExpectedDisagreement (Atom := Atom) q a := by
          rw [finiteRegionCouplingExpectedDisagreement_eq_map_eval_pair
            (q := q) (a := ⟨a, hΓΔ ha⟩)]

/-- Expand a finite region by one interaction-neighborhood layer. -/
noncomputable def expandRegion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) : Region Atom :=
  Λ ∪ Λ.biUnion M.atomInteractionNeighborhood

/-- Iterated expansion of a region by interaction neighborhoods. -/
noncomputable def iterExpandRegion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) : ℕ → Region Atom
  | 0 => Λ
  | n + 1 => M.expandRegion (M.iterExpandRegion Λ n)

theorem subset_expandRegion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) :
    Λ ⊆ M.expandRegion Λ := by
  intro a ha
  exact Finset.mem_union_left _ ha

theorem subset_iterExpandRegion_succ
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (n : ℕ) :
    M.iterExpandRegion Λ n ⊆ M.iterExpandRegion Λ (n + 1) := by
  exact M.subset_expandRegion (M.iterExpandRegion Λ n)

theorem atomInteractionNeighborhood_subset_iterExpandRegion_succ
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) {n : ℕ} {a : Atom}
    (ha : a ∈ M.iterExpandRegion Λ n) :
    M.atomInteractionNeighborhood a ⊆ M.iterExpandRegion Λ (n + 1) := by
  intro b hb
  simp only [iterExpandRegion, expandRegion]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hb⟩)

/-- Uniform bound on the finite-region Dobrushin constant under the
    uniform hypothesis. -/
theorem finiteRegionPairwiseDobrushinConstant_le_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C := by
  rcases hM with ⟨C, hC_nonneg, hC_lt_one, hC_row⟩
  refine ⟨C, hC_nonneg, hC_lt_one, ?_⟩
  intro Δ
  -- finiteRegionPairwiseDobrushinConstant Δ = sup_{a ∈ Δ} Σ_{b ∈ Δ} C(a,b)
  -- Each row sum Σ_{b ∈ Δ} C(a,b) ≤ Σ_{b ∈ nbhd(a)} C(a,b) ≤ C
  -- (since C(a,b) = 0 for b ∉ nbhd(a), and the full nbhd sum ≤ C by hC_row)
  by_cases hΔ : Δ.Nonempty
  · exact finiteRegionSupSeminorm_le_of_bound hC_nonneg (fun a ha => by
      let N := M.atomInteractionNeighborhood a
      have hEq :
          Finset.sum (Δ.filter fun b => b ∈ N) (fun b => M.pairwiseDobrushinCoefficient a b) =
            Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b) := by
        refine Finset.sum_subset (by intro b hb; exact (Finset.mem_filter.mp hb).1) ?_
        intro b hbΔ hbNotInter
        have hbNotN : b ∉ N := by
          intro hbN
          exact hbNotInter (Finset.mem_filter.mpr ⟨hbΔ, hbN⟩)
        exact M.pairwiseDobrushinCoefficient_eq_zero_of_not_mem_atomInteractionNeighborhood a b hbNotN
      have hLe :
          Finset.sum (Δ.filter fun b => b ∈ N) (fun b => M.pairwiseDobrushinCoefficient a b) ≤
            Finset.sum N (fun b => M.pairwiseDobrushinCoefficient a b) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (by intro b hb; exact (Finset.mem_filter.mp hb).2) ?_
        intro b hbN hbNotInter
        exact M.pairwiseDobrushinCoefficient_nonneg a b
      calc
        Finset.sum Δ (fun b => M.pairwiseDobrushinCoefficient a b)
          = Finset.sum (Δ.filter fun b => b ∈ N) (fun b => M.pairwiseDobrushinCoefficient a b) := by
              symm
              exact hEq
        _ ≤ Finset.sum N (fun b => M.pairwiseDobrushinCoefficient a b) := hLe
        _ ≤ C := hC_row a)
  · simp [finiteRegionPairwiseDobrushinConstant, finiteRegionSupSeminorm, hΔ, hC_nonneg]

/-- Partial heat-bath sweep coupling over an arbitrary sublist. -/
noncomputable def partialHeatBathSweepCouplingPMF
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (l : List (RegionAtom Atom Δ))
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ) :=
  l.foldl (fun r i => M.singleSiteHeatBathUpdateCouplingPMF i ξ r) q

/-- Partial sweep preserves first marginal. -/
theorem partialHeatBathSweepCouplingPMF_map_fst
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (l : List (RegionAtom Atom Δ))
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.partialHeatBathSweepCouplingPMF l ξ q).map Prod.fst =
      l.foldl (fun r i => M.singleSiteHeatBathUpdatePMF i ξ r) (q.map Prod.fst) := by
  unfold partialHeatBathSweepCouplingPMF
  induction l generalizing q with
  | nil => rfl
  | cons i is ih =>
      simp [List.foldl]
      rw [ih (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q)]
      rw [M.singleSiteHeatBathUpdateCouplingPMF_map_fst]

/-- Partial sweep preserves second marginal. -/
theorem partialHeatBathSweepCouplingPMF_map_snd
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (l : List (RegionAtom Atom Δ))
    (ξ : BoundaryCondition Atom)
    (q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ)) :
    (M.partialHeatBathSweepCouplingPMF l ξ q).map Prod.snd =
      l.foldl (fun r i => M.singleSiteHeatBathUpdatePMF i ξ r) (q.map Prod.snd) := by
  unfold partialHeatBathSweepCouplingPMF
  induction l generalizing q with
  | nil => rfl
  | cons i is ih =>
      simp [List.foldl]
      rw [ih (q := M.singleSiteHeatBathUpdateCouplingPMF i ξ q)]
      rw [M.singleSiteHeatBathUpdateCouplingPMF_map_snd]

/-- The DLR marginal is preserved by a partial sweep over interior sites. -/
theorem limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (l : List (RegionAtom Atom Δ))
    (ξ : BoundaryCondition Atom)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)))
    (hl : ∀ i ∈ l, M.atomInteractionNeighborhood i.1 ⊆ Δ) :
    l.foldl (fun r i => M.singleSiteHeatBathUpdatePMF i ξ r)
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF =
      (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (μ : Measure (InfiniteWorld Atom)) Δ).toPMF := by
  induction l with
  | nil => rfl
  | cons i is ih =>
      have hi_nbhd : M.atomInteractionNeighborhood i.1 ⊆ Δ := by
        exact hl i (by simp)
      have his : ∀ j ∈ is, M.atomInteractionNeighborhood j.1 ⊆ Δ := by
        intro j hj
        exact hl j (by simp [hj])
      simp [List.foldl]
      rw [M.limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior i ξ μ hμ hi_nbhd]
      simpa using ih his

private theorem exists_limitMarginalCoupling_sup_le_pow_of_uniformConstant
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
    (ξ : BoundaryCondition Atom) :
    ∀ n : ℕ, ∀ Λ : Region Atom,
      ∃ q : PMF (LocalAssignment Atom Λ × LocalAssignment Atom Λ),
        q.map Prod.fst =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) Λ).toPMF ∧
          q.map Prod.snd =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (ν : Measure (InfiniteWorld Atom)) Λ).toPMF ∧
          finiteRegionSupSeminorm Λ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ≤ C ^ n := by
  intro n
  induction n with
  | zero =>
      intro Λ
      let pμ :=
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (μ : Measure (InfiniteWorld Atom)) Λ).toPMF
      let pν :=
        (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν : Measure (InfiniteWorld Atom)) Λ).toPMF
      refine ⟨pmfMaximalCoupling pμ pν, ?_, ?_, ?_⟩
      · exact pmfMaximalCoupling_map_fst pμ pν
      · exact pmfMaximalCoupling_map_snd pμ pν
      · calc
          finiteRegionSupSeminorm Λ
              (finiteRegionCouplingExpectedDisagreement (Atom := Atom)
                (pmfMaximalCoupling pμ pν))
            ≤ finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom)
                (pmfMaximalCoupling pμ pν) := by
                  exact
                    finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_le_assignmentDisagreementProbability
                      (Atom := Atom) (pmfMaximalCoupling pμ pν)
          _ = pmfTotalVariation pμ pν := by
                unfold finiteRegionCouplingAssignmentDisagreementProbability
                simpa using pmfMaximalCoupling_disagreementProbability_eq_totalVariation pμ pν
          _ ≤ 1 := pmfTotalVariation_le_one pμ pν
          _ = C ^ 0 := by simp
  | succ n ih =>
      intro Λ
      let Δ := M.expandRegion Λ
      let hΛΔ : Λ ⊆ Δ := M.subset_expandRegion Λ
      rcases ih Δ with ⟨qΔ, hqfstΔ, hqsndΔ, hsupΔ⟩
      let emb : RegionAtom Atom Λ → RegionAtom Atom Δ := fun a => ⟨a.1, hΛΔ a.2⟩
      let lset : Finset (RegionAtom Atom Δ) := Λ.attach.image emb
      let l : List (RegionAtom Atom Δ) := lset.toList
      have hNodup : l.Nodup := by
        simpa [l] using lset.nodup_toList
      have hl_interior : ∀ i ∈ l, M.atomInteractionNeighborhood i.1 ⊆ Δ := by
        intro i hi
        have hi' : i ∈ lset := by simpa [l] using hi
        rcases Finset.mem_image.mp hi' with ⟨a, ha, rfl⟩
        simpa [Δ, iterExpandRegion] using
          (M.atomInteractionNeighborhood_subset_iterExpandRegion_succ
            (Λ := Λ) (n := 0) a.2)
      let qs := M.partialHeatBathSweepCouplingPMF l ξ qΔ
      let qΛ := projectCouplingToSubregion hΛΔ qs
      have hfst_qs :
          qs.map Prod.fst =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) Δ).toPMF := by
        dsimp [qs]
        rw [M.partialHeatBathSweepCouplingPMF_map_fst]
        rw [hqfstΔ]
        exact M.limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList l ξ μ hμ hl_interior
      have hsnd_qs :
          qs.map Prod.snd =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (ν : Measure (InfiniteWorld Atom)) Δ).toPMF := by
        dsimp [qs]
        rw [M.partialHeatBathSweepCouplingPMF_map_snd]
        rw [hqsndΔ]
        exact M.limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList l ξ ν hν hl_interior
      have hfst_qΛ :
          qΛ.map Prod.fst =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (μ : Measure (InfiniteWorld Atom)) Λ).toPMF := by
        dsimp [qΛ]
        rw [projectCouplingToSubregion_map_fst]
        rw [hfst_qs]
        exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) μ hΛΔ
      have hsnd_qΛ :
          qΛ.map Prod.snd =
            (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
              (ν : Measure (InfiniteWorld Atom)) Λ).toPMF := by
        dsimp [qΛ]
        rw [projectCouplingToSubregion_map_snd]
        rw [hsnd_qs]
        exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) ν hΛΔ
      have hs_nonneg : 0 ≤ C ^ n := by exact pow_nonneg hC_nonneg n
      have hs : ∀ a ∈ Δ,
          finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΔ a ≤ C ^ n := by
        intro a ha
        exact le_trans
          (le_finiteRegionSupSeminorm
            (Λ := Δ)
            (d := finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΔ) ha)
          hsupΔ
      have hconst_le_one : M.finiteRegionPairwiseDobrushinConstant Δ ≤ 1 := by
        exact le_trans (hC_bound Δ) (le_of_lt hC_lt_one)
      have hcontrol :=
        M.finiteRegionCouplingExpectedDisagreement_foldl_singleSiteHeatBathUpdateCoupling_control
          (Δ := Δ) (l := l) hNodup ξ qΔ (C ^ n) hs_nonneg hs hconst_le_one
      rcases hcontrol with ⟨_, hupdated, _⟩
      have hsup_qΛ :
          finiteRegionSupSeminorm Λ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΛ) ≤ C ^ (n + 1) := by
        refine finiteRegionSupSeminorm_le_of_bound
          (c := C ^ (n + 1))
          (pow_nonneg hC_nonneg (n + 1)) ?_
        intro a ha
        let aΛ : RegionAtom Atom Λ := ⟨a, ha⟩
        let aΔ : RegionAtom Atom Δ := emb aΛ
        have ha_mem_lset : aΔ ∈ lset := by
          refine Finset.mem_image.mpr ?_
          exact ⟨aΛ, by simp [aΔ, emb]⟩
        have ha_mem_l : aΔ ∈ l := by
          simpa [l] using ha_mem_lset
        calc
          finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΛ a
            = finiteRegionCouplingExpectedDisagreement (Atom := Atom) qs a := by
                simpa [qΛ, qs] using
                  (finiteRegionCouplingExpectedDisagreement_projectCoupling_eq
                    (Atom := Atom) hΛΔ qs a ha)
          _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ * C ^ n := by
                simpa [qs] using hupdated aΔ ha_mem_l
          _ ≤ C * C ^ n := by
                exact mul_le_mul_of_nonneg_right (hC_bound Δ) hs_nonneg
          _ = C ^ (n + 1) := by
                simp [pow_succ, mul_comm]
      exact ⟨qΛ, hfst_qΛ, hsnd_qΛ, hsup_qΛ⟩

/-- **Dobrushin uniqueness theorem** (uniform version): under
    `PaperUniformSmallTotalInfluence` (∃ C < 1 bounding all Dobrushin row sums),
    any two `FixedRegionCylinderDLR` probability measures on `InfiniteWorld Atom`
    are equal.

    The proof uses the Dobrushin contraction via descending shells:
    1. For a DLR measure μ, the Λ-marginal is a fixed point of the heat-bath
       update at every interior site (by
       `limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior`).
    2. For expanding regions `Λ_n = iterExpandRegion M Λ n`, a partial sweep
       coupling on `Λ_{k+1}` over the sites of `Λ_k` contracts disagreement
       by the uniform constant `C` while preserving the marginals.
    3. Projecting the coupling down through shells `Λ_n → ... → Λ_0 = Λ`
       gives TV(μ,ν,Λ) ≤ |Λ| · C^n → 0. -/
theorem paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    M.PaperUniqueMeasure := by
  rcases M.finiteRegionPairwiseDobrushinConstant_le_uniform hM with ⟨C, hC_nonneg, hC_lt_one, hC_bound⟩
  apply M.paperUniqueMeasure_of_finiteRegionAssignmentTotalVariation_eq_zero
  intro μ ν hμ hν Δ
  have hcoupling :
      ∀ n : ℕ,
        ∃ q : PMF (LocalAssignment Atom Δ × LocalAssignment Atom Δ),
          q.map Prod.fst =
              (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (μ : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
            q.map Prod.snd =
              (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
                (ν : Measure (InfiniteWorld Atom)) Δ).toPMF ∧
            finiteRegionSupSeminorm Δ
              (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ≤ C ^ n := by
    intro n
    exact exists_limitMarginalCoupling_sup_le_pow_of_uniformConstant
      (M := M) hC_nonneg hC_lt_one hC_bound μ ν hμ hν (fun _ => false) n Δ
  have htv_bound :
      ∀ n : ℕ,
        M.finiteRegionAssignmentTotalVariation μ ν Δ ≤ (Δ.card : ℝ) * C ^ n := by
    intro n
    rcases hcoupling n with ⟨q, hqfst, hqsnd, hsup⟩
    calc
      M.finiteRegionAssignmentTotalVariation μ ν Δ
        ≤ (Δ.card : ℝ) *
            finiteRegionSupSeminorm Δ
              (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
                exact M.finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
                  μ ν Δ q hqfst hqsnd
      _ ≤ (Δ.card : ℝ) * C ^ n := by
            exact mul_le_mul_of_nonneg_left hsup (by positivity)
  have htv_nonneg := M.finiteRegionAssignmentTotalVariation_nonneg μ ν Δ
  by_contra htv_ne
  have htv_pos : 0 < M.finiteRegionAssignmentTotalVariation μ ν Δ := by
    exact lt_of_le_of_ne htv_nonneg (Ne.symm htv_ne)
  have hpow0 := tendsto_pow_atTop_nhds_zero_of_lt_one hC_nonneg hC_lt_one
  have hε_pos :
      0 < M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1) := by
    positivity
  have hEventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        C ^ n <
          M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1) := by
    exact hpow0.eventually (Iio_mem_nhds hε_pos)
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  have hpow_lt :
      C ^ N <
        M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1) := by
    exact hN N le_rfl
  have hden_pos : 0 < ((Δ.card : ℝ) + 1) := by positivity
  by_cases hcard0 : (Δ.card : ℝ) = 0
  · have htv_le_zero : M.finiteRegionAssignmentTotalVariation μ ν Δ ≤ 0 := by
      simpa [hcard0] using htv_bound N
    linarith
  · have hcard_pos : 0 < (Δ.card : ℝ) := by
      have hcard_nonneg : 0 ≤ (Δ.card : ℝ) := by positivity
      exact lt_of_le_of_ne hcard_nonneg (Ne.symm hcard0)
    have hmul_lt₁ :
        (Δ.card : ℝ) * C ^ N <
          (Δ.card : ℝ) *
            (M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1)) := by
      exact mul_lt_mul_of_pos_left hpow_lt hcard_pos
    have hfrac_lt_one : (Δ.card : ℝ) / ((Δ.card : ℝ) + 1) < 1 := by
      rw [div_lt_iff₀ hden_pos]
      nlinarith
    have hmul_lt₂ :
        (Δ.card : ℝ) *
            (M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1)) <
          M.finiteRegionAssignmentTotalVariation μ ν Δ := by
      have hrewrite :
          (Δ.card : ℝ) *
              (M.finiteRegionAssignmentTotalVariation μ ν Δ / ((Δ.card : ℝ) + 1)) =
            ((Δ.card : ℝ) / ((Δ.card : ℝ) + 1)) *
              M.finiteRegionAssignmentTotalVariation μ ν Δ := by
        ring
      rw [hrewrite]
      simpa [one_mul] using mul_lt_mul_of_pos_right hfrac_lt_one htv_pos
    have : M.finiteRegionAssignmentTotalVariation μ ν Δ <
        M.finiteRegionAssignmentTotalVariation μ ν Δ := by
      exact lt_of_le_of_lt (htv_bound N) (lt_trans hmul_lt₁ hmul_lt₂)
    exact (lt_irrefl _ this).elim

end ClassicalInfiniteGroundMLNSpec

end Mettapedia.Logic.PLNMarkovLogicInfiniteUniqueness
