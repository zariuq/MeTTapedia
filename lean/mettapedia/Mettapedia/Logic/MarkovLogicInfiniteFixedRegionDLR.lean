import Mettapedia.Logic.MarkovLogicInfiniteCylinderDLR

/-!
# Infinite MLN Fixed-Region Cylinder DLR Preliminaries

This module starts the fixed-region DLR lane identified by the current infinite
MLN roadmap.

The key new ingredient is a finite-dependence theorem for boundary-conditioned
finite-volume kernels:

- for a fixed finite region `Λ`,
- and a fixed cylinder event `cylinder I S`,
- the probability assigned by the finite-volume world measure on `Λ`
  depends only on
  - the outside atoms from `I`, and
  - the outside atoms mentioned by clauses touching `Λ`.

This is the load-bearing prerequisite for the next genuine DLR theorem:
cluster-point or projective-limit candidate measures satisfying the
fixed-region cylinder law

`∫ γ_Λ(MeasureTheory.cylinder I S | ω) ∂μ = μ (MeasureTheory.cylinder I S)`.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR

open MeasureTheory
open scoped BigOperators
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfinitePositive

namespace GroundClause

variable {Atom : Type*} [DecidableEq Atom]

/-- Clause satisfaction depends only on the truth values of the atoms mentioned
by the clause. -/
theorem holds_congr_of_agreeOnAtoms
    (C : GroundClause Atom) {W₁ W₂ : AtomValuation Atom}
    (hag : ∀ a, a ∈ C.atoms → W₁ a = W₂ a) :
    C.holds W₁ ↔ C.holds W₂ := by
  constructor
  · intro h
    rcases h with ⟨l, hl, hholds⟩
    refine ⟨l, hl, ?_⟩
    cases l with
    | pos a =>
        have ha :
            a ∈ C.atoms :=
          Mettapedia.Logic.MarkovLogicClauseSemantics.GroundClause.atom_mem_atoms hl
        simp [Literal.holds] at hholds ⊢
        calc
          W₂ a = W₁ a := (hag a ha).symm
          _ = true := hholds
    | neg a =>
        have ha :
            a ∈ C.atoms :=
          Mettapedia.Logic.MarkovLogicClauseSemantics.GroundClause.atom_mem_atoms hl
        simp [Literal.holds] at hholds ⊢
        calc
          W₂ a = W₁ a := (hag a ha).symm
          _ = false := hholds
  · intro h
    rcases h with ⟨l, hl, hholds⟩
    refine ⟨l, hl, ?_⟩
    cases l with
    | pos a =>
        have ha :
            a ∈ C.atoms :=
          Mettapedia.Logic.MarkovLogicClauseSemantics.GroundClause.atom_mem_atoms hl
        simp [Literal.holds] at hholds ⊢
        calc
          W₁ a = W₂ a := hag a ha
          _ = true := hholds
    | neg a =>
        have ha :
            a ∈ C.atoms :=
          Mettapedia.Logic.MarkovLogicClauseSemantics.GroundClause.atom_mem_atoms hl
        simp [Literal.holds] at hholds ⊢
        calc
          W₁ a = W₂ a := hag a ha
          _ = false := hholds

/-- Patching the same local assignment into two boundary conditions yields the
same clause truth value when the boundary conditions agree on all outside atoms
mentioned by the clause. -/
theorem holds_patch_congr_of_boundaryAgreement
    (C : GroundClause Atom)
    (Λ : Region Atom)
    (x : LocalAssignment Atom Λ)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : ∀ a, a ∈ C.atoms → a ∉ Λ → ξ₁ a = ξ₂ a) :
    C.holds (patch Λ x ξ₁) ↔ C.holds (patch Λ x ξ₂) := by
  apply holds_congr_of_agreeOnAtoms
  intro a ha
  by_cases hΛ : a ∈ Λ
  · simp [patch, hΛ]
  · simp [patch, hΛ, hag a ha hΛ]

end GroundClause

namespace WeightedGroundClause

variable {Atom : Type*} [DecidableEq Atom]

/-- The potential of a weighted clause on a patched world depends only on the
outside atoms from the clause scope. -/
theorem eval_patch_eq_of_boundaryAgreement
    (wc : WeightedGroundClause Atom)
    (Λ : Region Atom)
    (x : LocalAssignment Atom Λ)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : ∀ a, a ∈ wc.clause.atoms → a ∉ Λ → ξ₁ a = ξ₂ a) :
    wc.eval (patch Λ x ξ₁) = wc.eval (patch Λ x ξ₂) := by
  classical
  unfold WeightedGroundClause.eval
  have hholds :=
    GroundClause.holds_patch_congr_of_boundaryAgreement wc.clause Λ x hag
  by_cases hs : wc.clause.holds (patch Λ x ξ₁)
  · have ht : wc.clause.holds (patch Λ x ξ₂) := hholds.mp hs
    simp [hs, ht]
  · have ht : ¬ wc.clause.holds (patch Λ x ξ₂) := by
      intro h
      exact hs (hholds.mpr h)
    simp [hs, ht]

end WeightedGroundClause

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

theorem clauseTouchesRegion_mono
    {C : GroundClause Atom} {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ) :
    clauseTouchesRegion C Λ → clauseTouchesRegion C Δ := by
  rintro ⟨a, haC, haΛ⟩
  exact ⟨a, haC, hΛΔ haΛ⟩

theorem regionSupport_mono
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ) :
    M.regionSupport Λ ⊆ M.regionSupport Δ := by
  intro j hj
  exact M.regionSupport_complete
    (clauseTouchesRegion_mono (C := (M.clauseData j).clause) hΛΔ
      (M.regionSupport_sound hj))

/-- The outside part of `Δ` relative to a nested subregion `Λ ⊆ Δ`. -/
def outsideRegion
    (Λ Δ : Region Atom) : Region Atom :=
  Δ \ Λ

/-- Restrict a `Δ`-assignment to the nested subregion `Λ`. -/
def restrictAssignment
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (x : LocalAssignment Atom Δ) :
    LocalAssignment Atom Λ :=
  fun a => x ⟨a.1, hΛΔ a.2⟩

/-- Restrict a `Δ`-assignment to the outside part `Δ \ Λ`. -/
def restrictOutsideAssignment
    {Λ Δ : Region Atom}
    (x : LocalAssignment Atom Δ) :
    LocalAssignment Atom (outsideRegion Λ Δ) :=
  fun a => x ⟨a.1, by
    exact (Finset.mem_sdiff.mp a.2).1⟩

/-- Merge an inside assignment on `Λ` and an outside assignment on `Δ \ Λ` into
an assignment on the whole region `Δ`. -/
def mergeAssignments
    {Λ Δ : Region Atom}
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ)) :
    LocalAssignment Atom Δ :=
  fun a =>
    if ha : a.1 ∈ Λ then
      xΛ ⟨a.1, ha⟩
    else
      xOut ⟨a.1, by
        exact Finset.mem_sdiff.mpr ⟨a.2, ha⟩⟩

@[simp] theorem restrictAssignment_mergeAssignments
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ)) :
    restrictAssignment (Atom := Atom) hΛΔ (mergeAssignments (Atom := Atom) xΛ xOut) = xΛ := by
  funext a
  simp [restrictAssignment, mergeAssignments, a.2]

@[simp] theorem restrictOutsideAssignment_mergeAssignments
    {Λ Δ : Region Atom}
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ)) :
    restrictOutsideAssignment (Atom := Atom) (mergeAssignments (Atom := Atom) xΛ xOut) = xOut := by
  funext a
  have hnot : a.1 ∉ Λ := (Finset.mem_sdiff.mp a.2).2
  simp [restrictOutsideAssignment, mergeAssignments, hnot]

@[simp] theorem mergeAssignments_restrict
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (x : LocalAssignment Atom Δ) :
    mergeAssignments (Atom := Atom)
      (restrictAssignment (Atom := Atom) hΛΔ x)
      (restrictOutsideAssignment (Atom := Atom) x) = x := by
  funext a
  by_cases ha : a.1 ∈ Λ
  · simp [mergeAssignments, restrictAssignment, ha]
  · simp [mergeAssignments, restrictOutsideAssignment, ha]

/-- Patching a merged `Δ`-assignment into `ξ` is the same as first patching the
outside part `Δ \ Λ` into `ξ` and then patching the inside part `Λ`. -/
theorem patch_mergeAssignments
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom) :
    patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ =
      patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) := by
  funext a
  by_cases haΔ : a ∈ Δ
  · by_cases haΛ : a ∈ Λ
    · simp [patch, mergeAssignments, haΔ, haΛ]
    · simp [outsideRegion, patch, mergeAssignments, haΔ, haΛ]
  · have hnotOut : a ∉ outsideRegion Λ Δ := by
      simp [outsideRegion, haΔ]
    by_cases haΛ : a ∈ Λ
    · exact (haΔ (hΛΔ haΛ)).elim
    · simp [outsideRegion, patch, haΔ, haΛ]

/-- The outside residual factor contributed by clauses touching `Δ` but not
`Λ`. It depends only on the outside assignment `Δ \ Λ` and the ambient boundary
condition. -/
noncomputable def outsideResidualWeight
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ Δ : Region Atom)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom) : ENNReal :=
  Finset.prod (M.regionSupport Δ \ M.regionSupport Λ) fun j =>
    (M.clauseData j).eval (patch (outsideRegion Λ Δ) xOut ξ)

theorem atom_not_mem_region_of_not_mem_regionSupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Region Atom}
    {j : ClauseId}
    (hj : j ∉ M.regionSupport Λ)
    {a : Atom}
    (ha : a ∈ (M.clauseData j).clause.atoms) :
    a ∉ Λ := by
  intro haΛ
  exact hj (M.regionSupport_complete ⟨a, ha, haΛ⟩)

theorem patch_mergeAssignments_eq_patchOutside_of_not_mem
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom)
    {a : Atom}
    (ha : a ∉ Λ) :
    patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ a =
      patch (outsideRegion Λ Δ) xOut ξ a := by
  calc
    patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ a
        = patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) a := by
            simpa using congrArg (fun ω => ω a) (patch_mergeAssignments (Atom := Atom) hΛΔ xΛ xOut ξ)
    _ = patch (outsideRegion Λ Δ) xOut ξ a := by
          simp [patch, ha]

theorem outsideResidualWeight_eq_prod_sdiff
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom) :
    outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ =
      Finset.prod (M.regionSupport Δ \ M.regionSupport Λ) (fun j =>
        (M.clauseData j).eval
          (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)) := by
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hjΛ : j ∉ M.regionSupport Λ := by
    exact (Finset.mem_sdiff.mp hj).2
  have hholds :
      (M.clauseData j).clause.holds (patch (outsideRegion Λ Δ) xOut ξ) ↔
        (M.clauseData j).clause.holds
          (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ) := by
    apply GroundClause.holds_congr_of_agreeOnAtoms
    intro a ha
    symm
    exact patch_mergeAssignments_eq_patchOutside_of_not_mem
      (Atom := Atom) hΛΔ xΛ xOut ξ
      (atom_not_mem_region_of_not_mem_regionSupport M hjΛ ha)
  unfold WeightedGroundClause.eval
  by_cases hs : (M.clauseData j).clause.holds (patch (outsideRegion Λ Δ) xOut ξ)
  · have ht :
        (M.clauseData j).clause.holds
          (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ) :=
      hholds.mp hs
    simp [hs, ht]
  · have ht :
        ¬ (M.clauseData j).clause.holds
            (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ) := by
      intro ht
      exact hs (hholds.mpr ht)
    simp [hs, ht]

theorem finiteVolumeWeight_mergeAssignments_eq
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom) :
    M.finiteVolumeWeight Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ =
      M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) *
        outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
  classical
  have hs : M.regionSupport Λ ⊆ M.regionSupport Δ := regionSupport_mono M hΛΔ
  calc
    M.finiteVolumeWeight Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ
        = Finset.prod (M.regionSupport Δ) (fun j =>
            (M.clauseData j).eval
              (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)) := by
            rfl
    _ = Finset.prod (M.regionSupport Δ \ M.regionSupport Λ) (fun j =>
            (M.clauseData j).eval
              (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)) *
          Finset.prod (M.regionSupport Λ) (fun j =>
            (M.clauseData j).eval
              (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)) := by
            symm
            exact Finset.prod_sdiff hs
    _ = Finset.prod (M.regionSupport Δ \ M.regionSupport Λ) (fun j =>
            (M.clauseData j).eval
              (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)) *
          Finset.prod (M.regionSupport Λ) (fun j =>
            (M.clauseData j).eval
              (patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ))) := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro j hj
            simp [patch_mergeAssignments (Atom := Atom) hΛΔ xΛ xOut ξ]
    _ = outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ *
          M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) := by
            rw [outsideResidualWeight_eq_prod_sdiff M hΛΔ xΛ xOut ξ]
            simp [InfiniteGroundMLNSpec.finiteVolumeWeight]
    _ = M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) *
          outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
            rw [mul_comm]

/-- Splitting a `Δ`-assignment into its inside and outside parts is an
equivalence. -/
noncomputable def finiteVolumeAssignmentSplitEquiv
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ) :
    LocalAssignment Atom Δ ≃
      (LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ)) where
  toFun x :=
    (restrictAssignment (Atom := Atom) hΛΔ x,
      restrictOutsideAssignment (Atom := Atom) x)
  invFun p :=
    mergeAssignments (Atom := Atom) p.1 p.2
  left_inv x :=
    mergeAssignments_restrict (Atom := Atom) hΛΔ x
  right_inv p := by
    rcases p with ⟨xΛ, xOut⟩
    simp

/-- The finite-volume partition on `Δ` factors over the inside assignments on
`Λ` and the outside assignments on `Δ \ Λ`. -/
theorem finiteVolumePartition_split
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (ξ : BoundaryCondition Atom) :
    M.finiteVolumePartition Δ ξ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ *
          M.finiteVolumePartition Λ (patch (outsideRegion Λ Δ) xOut ξ) := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumePartition
  calc
    ∑ x : LocalAssignment Atom Δ, M.finiteVolumeWeight Δ x ξ
        =
      ∑ p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ),
        M.finiteVolumeWeight Δ
          (mergeAssignments (Atom := Atom) p.1 p.2) ξ := by
            simpa [finiteVolumeAssignmentSplitEquiv] using
              (Fintype.sum_equiv
                (finiteVolumeAssignmentSplitEquiv (Atom := Atom) hΛΔ)
                (fun x : LocalAssignment Atom Δ => M.finiteVolumeWeight Δ x ξ)
                (fun p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ) =>
                  M.finiteVolumeWeight Δ
                    (mergeAssignments (Atom := Atom) p.1 p.2) ξ)
                (fun x => by
                  simp [finiteVolumeAssignmentSplitEquiv]))
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        ∑ xΛ : LocalAssignment Atom Λ,
          M.finiteVolumeWeight Δ
            (mergeAssignments (Atom := Atom) xΛ xOut) ξ := by
              rw [Fintype.sum_prod_type_right]
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        ∑ xΛ : LocalAssignment Atom Λ,
          M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) *
            outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              refine Finset.sum_congr rfl ?_
              intro xΛ hxΛ
              exact finiteVolumeWeight_mergeAssignments_eq M hΛΔ xΛ xOut ξ
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        (∑ xΛ : LocalAssignment Atom Λ,
          M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ)) *
            outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              rw [Finset.sum_mul]
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        M.finiteVolumePartition Λ (patch (outsideRegion Λ Δ) xOut ξ) *
          outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              rfl
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ *
          M.finiteVolumePartition Λ (patch (outsideRegion Λ Δ) xOut ξ) := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              rw [mul_comm]

/-- Unnormalized cylinder mass for a finite-volume kernel. -/
noncomputable def finiteVolumeCylinderMass
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (I : Region Atom) (S : Set (LocalAssignment Atom I)) : ENNReal :=
  by
    classical
    exact
      ∑ x : LocalAssignment Atom Λ,
        if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
          M.finiteVolumeWeight Λ x ξ
        else 0

/-- The finite-volume probability of a cylinder event is the corresponding
unnormalized cylinder mass divided by the partition function. -/
theorem finiteVolumeWorldMeasure_cylinder
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    finiteVolumeWorldMeasure M Λ ξ hZ (MeasureTheory.cylinder I S) =
      finiteVolumeCylinderMass M Λ ξ I S * (M.finiteVolumePartition Λ ξ)⁻¹ := by
  classical
  unfold finiteVolumeWorldMeasure finiteVolumeWorldPMF finiteVolumeCylinderMass
  rw [PMF.toMeasure_map_apply
    (p := finiteVolumeAssignmentPMF M Λ ξ hZ)
    (f := fun x : LocalAssignment Atom Λ => patch Λ x ξ)
    (s := MeasureTheory.cylinder I S)
    (hf := measurable_patch Λ ξ)
    (hs := hS.cylinder I)]
  rw [PMF.toMeasure_apply_fintype]
  simp_rw [Set.indicator_apply, finiteVolumeAssignmentPMF_apply]
  have hsum :
      (∑ x : LocalAssignment Atom Λ,
        if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
          M.finiteVolumeWeight Λ x ξ * (M.finiteVolumePartition Λ ξ)⁻¹
        else 0) =
      (∑ x : LocalAssignment Atom Λ,
        if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
          M.finiteVolumeWeight Λ x ξ
        else 0) * (M.finiteVolumePartition Λ ξ)⁻¹ := by
    calc
      (∑ x : LocalAssignment Atom Λ,
        if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
          M.finiteVolumeWeight Λ x ξ * (M.finiteVolumePartition Λ ξ)⁻¹
        else 0)
          =
        ∑ x : LocalAssignment Atom Λ,
          (if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
            M.finiteVolumeWeight Λ x ξ
          else 0) * (M.finiteVolumePartition Λ ξ)⁻¹ := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases hxS : patch Λ x ξ ∈ MeasureTheory.cylinder I S <;> simp [hxS]
      _ = (∑ x : LocalAssignment Atom Λ,
            if patch Λ x ξ ∈ MeasureTheory.cylinder I S then
              M.finiteVolumeWeight Λ x ξ
            else 0) * (M.finiteVolumePartition Λ ξ)⁻¹ := by
              rw [← Finset.sum_mul]
  simp_rw [Set.mem_preimage] at *
  rw [hsum]

/-- The unnormalized cylinder mass on `Δ` factors over inside assignments on `Λ`
and outside assignments on `Δ \ Λ`. -/
theorem finiteVolumeCylinderMass_split
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (ξ : BoundaryCondition Atom)
    (I : Region Atom) (S : Set (LocalAssignment Atom I)) :
    finiteVolumeCylinderMass M Δ ξ I S =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ *
          finiteVolumeCylinderMass M Λ (patch (outsideRegion Λ Δ) xOut ξ) I S := by
  classical
  unfold finiteVolumeCylinderMass
  calc
    (∑ x : LocalAssignment Atom Δ,
      if patch Δ x ξ ∈ MeasureTheory.cylinder I S then
        M.finiteVolumeWeight Δ x ξ
      else 0)
        =
      (∑ p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ),
        if patch Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ ∈ MeasureTheory.cylinder I S then
          M.finiteVolumeWeight Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ
        else 0) := by
            simpa [finiteVolumeAssignmentSplitEquiv] using
              (Fintype.sum_equiv
                (finiteVolumeAssignmentSplitEquiv (Atom := Atom) hΛΔ)
                (fun x : LocalAssignment Atom Δ =>
                  if patch Δ x ξ ∈ MeasureTheory.cylinder I S then
                    M.finiteVolumeWeight Δ x ξ
                  else 0)
                (fun p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ) =>
                  if patch Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ ∈ MeasureTheory.cylinder I S then
                    M.finiteVolumeWeight Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ
                  else 0)
                (fun x => by
                  simp [finiteVolumeAssignmentSplitEquiv]))
    _ =
      (∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        ∑ xΛ : LocalAssignment Atom Λ,
          if patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ ∈ MeasureTheory.cylinder I S then
            M.finiteVolumeWeight Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ
          else 0) := by
              rw [Fintype.sum_prod_type_right]
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        ∑ xΛ : LocalAssignment Atom Λ,
          if patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S then
            M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) *
              outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ
          else 0 := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              refine Finset.sum_congr rfl ?_
              intro xΛ hxΛ
              simp [patch_mergeAssignments (Atom := Atom) hΛΔ xΛ xOut ξ,
                finiteVolumeWeight_mergeAssignments_eq M hΛΔ xΛ xOut ξ]
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        (∑ xΛ : LocalAssignment Atom Λ,
          if patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S then
            M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ)
          else 0) *
            outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              calc
                (∑ xΛ : LocalAssignment Atom Λ,
                  if patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S then
                    M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) *
                      outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ
                  else 0)
                    =
                ∑ xΛ : LocalAssignment Atom Λ,
                  (if patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S then
                    M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ)
                  else 0) *
                    outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
                      refine Finset.sum_congr rfl ?_
                      intro xΛ hxΛ
                      by_cases hxS : patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S <;>
                        simp [hxS]
                _ = (∑ xΛ : LocalAssignment Atom Λ,
                      if patch Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ) ∈ MeasureTheory.cylinder I S then
                        M.finiteVolumeWeight Λ xΛ (patch (outsideRegion Λ Δ) xOut ξ)
                      else 0) *
                      outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ := by
                        rw [Finset.sum_mul]
    _ =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        outsideResidualWeight (Atom := Atom) (ClauseId := ClauseId) M Λ Δ xOut ξ *
          finiteVolumeCylinderMass M Λ (patch (outsideRegion Λ Δ) xOut ξ) I S := by
              refine Finset.sum_congr rfl ?_
              intro xOut hxOut
              rw [finiteVolumeCylinderMass, mul_comm]

/-- Two boundary conditions agree on the outside atoms mentioned by every clause
touching `Λ`. This is the finite clause-support part of the fixed-region DLR
dependence statement. -/
def AgreesOnBoundarySupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) : Prop :=
  ∀ ⦃j a : _⦄,
    j ∈ M.regionSupport Λ →
      a ∈ (M.clauseData j).clause.atoms →
        a ∉ Λ →
          ξ₁ a = ξ₂ a

/-- Two boundary conditions agree on the outside atoms explicitly inspected by a
fixed cylinder event `cylinder I S`. -/
def AgreesOnCylinderOutside
    (Λ I : Region Atom)
    (ξ₁ ξ₂ : BoundaryCondition Atom) : Prop :=
  ∀ ⦃a : _⦄, a ∈ I → a ∉ Λ → ξ₁ a = ξ₂ a

/-- Finite outside-atom support contributed by clauses touching `Λ`. -/
noncomputable def boundaryClauseSupportRegion
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) : Region Atom :=
  (M.regionSupport Λ).biUnion fun j =>
    (M.clauseData j).clause.atoms \ Λ

/-- Finite combined boundary support for the `Λ`-kernel of a cylinder event. -/
noncomputable def cylinderBoundarySupportRegion
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom) : Region Atom :=
  boundaryClauseSupportRegion M Λ ∪ outsideRegion Λ I

theorem mem_boundaryClauseSupportRegion_of_regionSupport_atom
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ : Region Atom} {j : ClauseId} {a : Atom}
    (hj : j ∈ M.regionSupport Λ)
    (ha : a ∈ (M.clauseData j).clause.atoms)
    (hnot : a ∉ Λ) :
    a ∈ boundaryClauseSupportRegion M Λ := by
  classical
  exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_sdiff.mpr ⟨ha, hnot⟩⟩

omit [DecidableEq Atom] in
theorem eq_of_restrict_eq
    {J : Region Atom}
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hJ : Finset.restrict J ξ₁ = Finset.restrict J ξ₂)
    {a : Atom} (ha : a ∈ J) :
    ξ₁ a = ξ₂ a := by
  have h := congrArg (fun f => f ⟨a, ha⟩) hJ
  simpa [Finset.restrict] using h

theorem agreesOnBoundarySupport_of_restrict_cylinderBoundarySupportRegion_eq
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hrestrict :
      Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₁ =
        Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₂) :
    AgreesOnBoundarySupport M Λ ξ₁ ξ₂ := by
  intro j a hj ha hnot
  exact eq_of_restrict_eq hrestrict
    (Finset.mem_union.mpr <| Or.inl <|
      mem_boundaryClauseSupportRegion_of_regionSupport_atom M hj ha hnot)

theorem agreesOnCylinderOutside_of_restrict_cylinderBoundarySupportRegion_eq
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hrestrict :
      Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₁ =
        Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₂) :
    AgreesOnCylinderOutside Λ I ξ₁ ξ₂ := by
  intro a haI hnot
  exact eq_of_restrict_eq hrestrict
    (Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨haI, hnot⟩)

theorem finiteVolumeWeight_eq_of_agreesOnBoundarySupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (x : LocalAssignment Atom Λ)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOnBoundarySupport M Λ ξ₁ ξ₂) :
    M.finiteVolumeWeight Λ x ξ₁ = M.finiteVolumeWeight Λ x ξ₂ := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumeWeight
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact WeightedGroundClause.eval_patch_eq_of_boundaryAgreement
    (wc := M.clauseData j) (Λ := Λ) (x := x)
    (hag := fun a ha hnot => hag hj ha hnot)

theorem finiteVolumePartition_eq_of_agreesOnBoundarySupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOnBoundarySupport M Λ ξ₁ ξ₂) :
    M.finiteVolumePartition Λ ξ₁ = M.finiteVolumePartition Λ ξ₂ := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumePartition
  refine Finset.sum_congr rfl ?_
  intro x hx
  exact finiteVolumeWeight_eq_of_agreesOnBoundarySupport M Λ x hag

theorem finiteVolumeAssignmentPMF_eq_of_agreesOnBoundarySupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    {hZ₁ : M.finiteVolumePartition Λ ξ₁ ≠ 0}
    {hZ₂ : M.finiteVolumePartition Λ ξ₂ ≠ 0}
    (hag : AgreesOnBoundarySupport M Λ ξ₁ ξ₂) :
    finiteVolumeAssignmentPMF M Λ ξ₁ hZ₁ =
      finiteVolumeAssignmentPMF M Λ ξ₂ hZ₂ := by
  ext x
  rw [finiteVolumeAssignmentPMF_apply, finiteVolumeAssignmentPMF_apply]
  rw [finiteVolumeWeight_eq_of_agreesOnBoundarySupport M Λ x hag]
  rw [finiteVolumePartition_eq_of_agreesOnBoundarySupport M Λ hag]

theorem restrict_patch_eq_of_agreesOnCylinderOutside
    (Λ I : Region Atom)
    (x : LocalAssignment Atom Λ)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOnCylinderOutside Λ I ξ₁ ξ₂) :
    Finset.restrict I (patch Λ x ξ₁) =
      Finset.restrict I (patch Λ x ξ₂) := by
  funext a
  by_cases hΛ : a.1 ∈ Λ
  · simp [Finset.restrict, patch, hΛ]
  · simp [Finset.restrict, patch, hΛ, hag a.2 hΛ]

theorem preimage_cylinder_patch_eq_of_agreesOnCylinderOutside
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hag : AgreesOnCylinderOutside Λ I ξ₁ ξ₂) :
    (fun x : LocalAssignment Atom Λ => patch Λ x ξ₁) ⁻¹' MeasureTheory.cylinder I S =
      (fun x : LocalAssignment Atom Λ => patch Λ x ξ₂) ⁻¹' MeasureTheory.cylinder I S := by
  ext x
  simp [MeasureTheory.cylinder,
    restrict_patch_eq_of_agreesOnCylinderOutside Λ I x hag]

/-- Finite-volume world-measure probabilities on a fixed cylinder event depend
only on finitely many boundary coordinates:

- the outside atoms mentioned by clauses touching `Λ`, and
- the outside atoms occurring in the cylinder support `I`.

This is the main finite-dependence lemma needed before proving the true
fixed-region cylinder DLR theorem for global measures. -/
theorem finiteVolumeWorldMeasure_cylinder_eq_of_agreesOnBoundaryData
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    {hZ₁ : M.finiteVolumePartition Λ ξ₁ ≠ 0}
    {hZ₂ : M.finiteVolumePartition Λ ξ₂ ≠ 0}
    (hboundary : AgreesOnBoundarySupport M Λ ξ₁ ξ₂)
    (hcyl : AgreesOnCylinderOutside Λ I ξ₁ ξ₂) :
    finiteVolumeWorldMeasure M Λ ξ₁ hZ₁ (MeasureTheory.cylinder I S) =
      finiteVolumeWorldMeasure M Λ ξ₂ hZ₂ (MeasureTheory.cylinder I S) := by
  have hpmf :
      finiteVolumeAssignmentPMF M Λ ξ₁ hZ₁ =
        finiteVolumeAssignmentPMF M Λ ξ₂ hZ₂ :=
    finiteVolumeAssignmentPMF_eq_of_agreesOnBoundarySupport M Λ hboundary
  have hpre :=
    preimage_cylinder_patch_eq_of_agreesOnCylinderOutside Λ I S hcyl
  have hmeasure :
      (finiteVolumeAssignmentPMF M Λ ξ₁ hZ₁).toMeasure =
        (finiteVolumeAssignmentPMF M Λ ξ₂ hZ₂).toMeasure :=
    congrArg PMF.toMeasure hpmf
  unfold finiteVolumeWorldMeasure finiteVolumeWorldPMF
  rw [PMF.toMeasure_map_apply
    (p := finiteVolumeAssignmentPMF M Λ ξ₁ hZ₁)
    (f := fun x : LocalAssignment Atom Λ => patch Λ x ξ₁)
    (s := MeasureTheory.cylinder I S)
    (hf := measurable_patch Λ ξ₁)
    (hs := hS.cylinder I)]
  rw [PMF.toMeasure_map_apply
    (p := finiteVolumeAssignmentPMF M Λ ξ₂ hZ₂)
    (f := fun x : LocalAssignment Atom Λ => patch Λ x ξ₂)
    (s := MeasureTheory.cylinder I S)
    (hf := measurable_patch Λ ξ₂)
    (hs := hS.cylinder I)]
  rw [hpre]
  exact congrArg
    (fun ν =>
      ν ((fun x : LocalAssignment Atom Λ => patch Λ x ξ₂) ⁻¹'
        MeasureTheory.cylinder I S))
    hmeasure

/-- Finite-volume cylinder probabilities factor through the finite restriction
to the combined clause/cylinder boundary support. -/
theorem finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    {hZ₁ : M.finiteVolumePartition Λ ξ₁ ≠ 0}
    {hZ₂ : M.finiteVolumePartition Λ ξ₂ ≠ 0}
    (hrestrict :
      Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₁ =
        Finset.restrict (cylinderBoundarySupportRegion M Λ I) ξ₂) :
    finiteVolumeWorldMeasure M Λ ξ₁ hZ₁ (MeasureTheory.cylinder I S) =
      finiteVolumeWorldMeasure M Λ ξ₂ hZ₂ (MeasureTheory.cylinder I S) := by
  refine finiteVolumeWorldMeasure_cylinder_eq_of_agreesOnBoundaryData
    M Λ I S hS
    (agreesOnBoundarySupport_of_restrict_cylinderBoundarySupportRegion_eq M Λ I hrestrict)
    (agreesOnCylinderOutside_of_restrict_cylinderBoundarySupportRegion_eq M Λ I hrestrict)

namespace StrictlyPositiveInfiniteGroundMLNSpec

theorem finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq'
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    (hrestrict :
      Finset.restrict
          (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I) ξ₁ =
        Finset.restrict
          (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I) ξ₂) :
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ξ₁
        (MeasureTheory.cylinder I S) =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ξ₂
        (MeasureTheory.cylinder I S) := by
  simpa [StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure] using
    (finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq
      (M := M.toInfiniteGroundMLNSpec)
      (Λ := Λ) (I := I) (S := S) hS
      (ξ₁ := ξ₁) (ξ₂ := ξ₂)
      (hZ₁ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Λ ξ₁)
      (hZ₂ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Λ ξ₂)
      hrestrict)

noncomputable def cylinderBoundaryKernelValue
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (x : LocalAssignment Atom
      (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I)) :
    ENNReal :=
  StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
    (patch (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I) x
      (fun _ => false))
    (MeasureTheory.cylinder I S)

theorem cylinderBoundaryKernelValue_ne_top
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (x : LocalAssignment Atom
      (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I)) :
    StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S x ≠ (⊤ : ENNReal) := by
  classical
  dsimp [StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue]
  exact measure_ne_top _ _

theorem finiteVolumeWorldMeasure_cylinder_eq_cylinderBoundaryKernelValue
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S)
    (ω : InfiniteWorld Atom) :
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S) =
      StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
        (Finset.restrict
          (cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I) ω) := by
  let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
  let ω₀ : BoundaryCondition Atom :=
    patch J (Finset.restrict J ω) (fun _ => false)
  have hrestrict : Finset.restrict J ω = Finset.restrict J ω₀ := by
    funext a
    simp [ω₀, J, a.2]
  calc
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S)
      =
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω₀
        (MeasureTheory.cylinder I S) := by
          exact StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq'
            M
            Λ I S hS hrestrict
    _ =
    StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
      (Finset.restrict J ω) := by
          rfl

theorem measurable_finiteVolumeWorldMeasure_cylinder
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    Measurable
      (fun ω : InfiniteWorld Atom =>
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
          (MeasureTheory.cylinder I S)) := by
  let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
  have hg : Measurable
      (StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S) := by
    classical
    exact Measurable.of_discrete
  have hEq :
      (fun ω : InfiniteWorld Atom =>
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
          (MeasureTheory.cylinder I S)) =
      fun ω : InfiniteWorld Atom =>
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
          (Finset.restrict J ω) := by
    funext ω
    simpa [J] using
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_cylinderBoundaryKernelValue
        M Λ I S hS ω
  rw [hEq]
  exact hg.comp (Finset.measurable_restrict J)

end StrictlyPositiveInfiniteGroundMLNSpec

/-- For local query events supported inside `Λ`, only the clause-support part of
the boundary data matters. -/
theorem finiteVolumeWorldMeasure_localQueryEvent_eq_of_agreesOnBoundarySupport
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (q : LocalConstraintQuery Atom Λ)
    {ξ₁ ξ₂ : BoundaryCondition Atom}
    {hZ₁ : M.finiteVolumePartition Λ ξ₁ ≠ 0}
    {hZ₂ : M.finiteVolumePartition Λ ξ₂ ≠ 0}
    (hboundary : AgreesOnBoundarySupport M Λ ξ₁ ξ₂) :
    finiteVolumeWorldMeasure M Λ ξ₁ hZ₁ (localQueryEvent Λ q) =
      finiteVolumeWorldMeasure M Λ ξ₂ hZ₂ (localQueryEvent Λ q) := by
  rw [localQueryEvent_eq_cylinder Λ q]
  refine finiteVolumeWorldMeasure_cylinder_eq_of_agreesOnBoundaryData
    M Λ Λ (localConstraintSet Λ q) (measurableSet_localConstraintSet Λ q)
    hboundary ?_
  intro a ha hnot
  exact False.elim (hnot ha)

/-- For a nested finite-volume boundary obtained from a merged `Δ`-assignment,
the `Λ`-kernel on a cylinder event depends only on the outside part `Δ \ Λ`. -/
theorem finiteVolumeWorldMeasure_cylinder_patch_merge_eq_patchOutside
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (xΛ : LocalAssignment Atom Λ)
    (xOut : LocalAssignment Atom (outsideRegion Λ Δ))
    (ξ : BoundaryCondition Atom)
    (I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
      (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)
      (MeasureTheory.cylinder I S) =
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
      (patch (outsideRegion Λ Δ) xOut ξ)
      (MeasureTheory.cylinder I S) := by
  let ξ₁ : BoundaryCondition Atom :=
    patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ
  let ξ₂ : BoundaryCondition Atom :=
    patch (outsideRegion Λ Δ) xOut ξ
  have hag :
      ∀ ⦃a : Atom⦄, a ∉ Λ → ξ₁ a = ξ₂ a := by
    intro a hnot
    dsimp [ξ₁, ξ₂]
    exact patch_mergeAssignments_eq_patchOutside_of_not_mem
      (Atom := Atom) hΛΔ xΛ xOut ξ hnot
  have hboundary :
      AgreesOnBoundarySupport M.toInfiniteGroundMLNSpec Λ ξ₁ ξ₂ := by
    intro j a hj ha hnot
    exact hag hnot
  have hcyl :
      AgreesOnCylinderOutside Λ I ξ₁ ξ₂ := by
    intro a ha hnot
    exact hag hnot
  simpa [StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure, ξ₁, ξ₂] using
    (finiteVolumeWorldMeasure_cylinder_eq_of_agreesOnBoundaryData
      (M := M.toInfiniteGroundMLNSpec)
      (Λ := Λ) (I := I) (S := S) hS
      (ξ₁ := ξ₁) (ξ₂ := ξ₂)
      (hZ₁ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Λ ξ₁)
      (hZ₂ := StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Λ ξ₂)
      hboundary hcyl)

/-- Discrete finite-volume subregion DLR law on cylinders:
averaging the `Λ`-kernel against the `Δ`-assignment PMF reproduces the
`Δ`-cylinder probability. This is the finite combinatorial heart of the
fixed-region DLR theorem. -/
theorem finiteVolumeAssignmentPMF_subregion_cylinder_dlr
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (ξ : BoundaryCondition Atom)
    (I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    ∑ x : LocalAssignment Atom Δ,
      finiteVolumeAssignmentPMF
          (M := M.toInfiniteGroundMLNSpec)
          Δ ξ
          (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Δ ξ) x *
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ (patch Δ x ξ)
          (MeasureTheory.cylinder I S) =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Δ ξ
        (MeasureTheory.cylinder I S) := by
  classical
  let ZΔ : ENNReal := M.toInfiniteGroundMLNSpec.finiteVolumePartition Δ ξ
  let η :
      LocalAssignment Atom (outsideRegion Λ Δ) → BoundaryCondition Atom :=
    fun xOut => patch (outsideRegion Λ Δ) xOut ξ
  let ZΛ :
      LocalAssignment Atom (outsideRegion Λ Δ) → ENNReal :=
    fun xOut => M.toInfiniteGroundMLNSpec.finiteVolumePartition Λ (η xOut)
  let r :
      LocalAssignment Atom (outsideRegion Λ Δ) → ENNReal :=
    fun xOut => outsideResidualWeight
      (Atom := Atom) (ClauseId := ClauseId) M.toInfiniteGroundMLNSpec Λ Δ xOut ξ
  let mass :
      LocalAssignment Atom (outsideRegion Λ Δ) → ENNReal :=
    fun xOut => finiteVolumeCylinderMass
      M.toInfiniteGroundMLNSpec Λ (η xOut) I S
  let κ :
      LocalAssignment Atom (outsideRegion Λ Δ) → ENNReal :=
    fun xOut =>
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ (η xOut)
        (MeasureTheory.cylinder I S)
  have hZΔ :
      M.toInfiniteGroundMLNSpec.finiteVolumePartition Δ ξ ≠ 0 :=
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Δ ξ
  have hZΛ :
      ∀ xOut : LocalAssignment Atom (outsideRegion Λ Δ), ZΛ xOut ≠ 0 := by
    intro xOut
    exact StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Λ (η xOut)
  have hκ :
      ∀ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        κ xOut = mass xOut * (ZΛ xOut)⁻¹ := by
    intro xOut
    simpa [κ, mass, ZΛ, η, StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure] using
      (finiteVolumeWorldMeasure_cylinder
        (M := M.toInfiniteGroundMLNSpec)
        (Λ := Λ) (I := I) (S := S) hS
        (ξ := η xOut) (hZ := hZΛ xOut))
  have hsplit :
      (∑ x : LocalAssignment Atom Δ,
        finiteVolumeAssignmentPMF
            (M := M.toInfiniteGroundMLNSpec)
            Δ ξ hZΔ x *
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ (patch Δ x ξ)
            (MeasureTheory.cylinder I S))
        =
      ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
        ∑ xΛ : LocalAssignment Atom Λ,
          finiteVolumeAssignmentPMF
              (M := M.toInfiniteGroundMLNSpec)
              Δ ξ hZΔ
              (mergeAssignments (Atom := Atom) xΛ xOut) *
            StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
              (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)
              (MeasureTheory.cylinder I S) := by
    calc
      (∑ x : LocalAssignment Atom Δ,
        finiteVolumeAssignmentPMF
            (M := M.toInfiniteGroundMLNSpec)
            Δ ξ hZΔ x *
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ (patch Δ x ξ)
            (MeasureTheory.cylinder I S))
          =
        ∑ p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ),
          finiteVolumeAssignmentPMF
              (M := M.toInfiniteGroundMLNSpec)
              Δ ξ hZΔ
              (mergeAssignments (Atom := Atom) p.1 p.2) *
            StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
              (patch Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ)
              (MeasureTheory.cylinder I S) := by
                simpa [finiteVolumeAssignmentSplitEquiv] using
                  (Fintype.sum_equiv
                    (finiteVolumeAssignmentSplitEquiv (Atom := Atom) hΛΔ)
                    (fun x : LocalAssignment Atom Δ =>
                      finiteVolumeAssignmentPMF
                          (M := M.toInfiniteGroundMLNSpec)
                          Δ ξ hZΔ x *
                        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
                          (patch Δ x ξ) (MeasureTheory.cylinder I S))
                    (fun p : LocalAssignment Atom Λ × LocalAssignment Atom (outsideRegion Λ Δ) =>
                      finiteVolumeAssignmentPMF
                          (M := M.toInfiniteGroundMLNSpec)
                          Δ ξ hZΔ
                          (mergeAssignments (Atom := Atom) p.1 p.2) *
                        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
                          (patch Δ (mergeAssignments (Atom := Atom) p.1 p.2) ξ)
                          (MeasureTheory.cylinder I S))
                    (fun x => by
                      simp [finiteVolumeAssignmentSplitEquiv]))
      _ =
        ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
          ∑ xΛ : LocalAssignment Atom Λ,
            finiteVolumeAssignmentPMF
                (M := M.toInfiniteGroundMLNSpec)
                Δ ξ hZΔ
                (mergeAssignments (Atom := Atom) xΛ xOut) *
              StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
                (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)
                (MeasureTheory.cylinder I S) := by
                  rw [Fintype.sum_prod_type_right]
  rw [hsplit]
  calc
    (∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
      ∑ xΛ : LocalAssignment Atom Λ,
        finiteVolumeAssignmentPMF
            (M := M.toInfiniteGroundMLNSpec)
            Δ ξ hZΔ
            (mergeAssignments (Atom := Atom) xΛ xOut) *
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ
            (patch Δ (mergeAssignments (Atom := Atom) xΛ xOut) ξ)
            (MeasureTheory.cylinder I S))
      =
    ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
      ∑ xΛ : LocalAssignment Atom Λ,
        (M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ xΛ (η xOut)) *
          (r xOut * ZΔ⁻¹ * κ xOut) := by
            refine Finset.sum_congr rfl ?_
            intro xOut hxOut
            refine Finset.sum_congr rfl ?_
            intro xΛ hxΛ
            rw [finiteVolumeAssignmentPMF_apply]
            rw [finiteVolumeWorldMeasure_cylinder_patch_merge_eq_patchOutside
              (M := M) hΛΔ xΛ xOut ξ I S hS]
            rw [finiteVolumeWeight_mergeAssignments_eq
              (M := M.toInfiniteGroundMLNSpec) hΛΔ xΛ xOut ξ]
            simp [ZΔ, η, r, κ, mul_assoc, mul_left_comm, mul_comm]
    _ =
    ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
      (ZΛ xOut) * (r xOut * ZΔ⁻¹ * κ xOut) := by
        refine Finset.sum_congr rfl ?_
        intro xOut hxOut
        calc
          (∑ xΛ : LocalAssignment Atom Λ,
            M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ xΛ (η xOut) *
              (r xOut * ZΔ⁻¹ * κ xOut))
              =
          (∑ xΛ : LocalAssignment Atom Λ,
            M.toInfiniteGroundMLNSpec.finiteVolumeWeight Λ xΛ (η xOut)) *
              (r xOut * ZΔ⁻¹ * κ xOut) := by
                rw [Finset.sum_mul]
          _ = ZΛ xOut * (r xOut * ZΔ⁻¹ * κ xOut) := by
                rfl
    _ =
    ∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
      r xOut * mass xOut * ZΔ⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro xOut hxOut
        rw [hκ xOut]
        have htop : ZΛ xOut ≠ ⊤ :=
          finiteVolumePartition_ne_top M.toInfiniteGroundMLNSpec Λ (η xOut)
        calc
          ZΛ xOut * (r xOut * ZΔ⁻¹ * (mass xOut * (ZΛ xOut)⁻¹))
              = r xOut * mass xOut * (ZΛ xOut * (ZΛ xOut)⁻¹) * ZΔ⁻¹ := by
                  ac_rfl
          _ = r xOut * mass xOut * 1 * ZΔ⁻¹ := by
                rw [ENNReal.mul_inv_cancel (hZΛ xOut) htop]
          _ = r xOut * mass xOut * ZΔ⁻¹ := by
                simp [mul_assoc]
    _ =
    (∑ xOut : LocalAssignment Atom (outsideRegion Λ Δ),
      r xOut * mass xOut) * ZΔ⁻¹ := by
        rw [← Finset.sum_mul]
    _ =
    finiteVolumeCylinderMass M.toInfiniteGroundMLNSpec Δ ξ I S * ZΔ⁻¹ := by
      rw [finiteVolumeCylinderMass_split
        (M := M.toInfiniteGroundMLNSpec) hΛΔ ξ I S]
    _ =
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Δ ξ
      (MeasureTheory.cylinder I S) := by
        simpa [ZΔ, StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure] using
          (finiteVolumeWorldMeasure_cylinder
            (M := M.toInfiniteGroundMLNSpec)
            (Λ := Δ) (I := I) (S := S) hS
            (ξ := ξ) (hZ := hZΔ)).symm

/-- Finite-volume fixed-region DLR law in measure/`lintegral` form. -/
theorem finiteVolumeWorldMeasure_subregion_cylinder_dlr
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ)
    (ξ : BoundaryCondition Atom)
    (I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    ∫⁻ ω,
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S)
      ∂ StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Δ ξ =
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Δ ξ
        (MeasureTheory.cylinder I S) := by
  classical
  let p : PMF (LocalAssignment Atom Δ) :=
    finiteVolumeAssignmentPMF
      (M := M.toInfiniteGroundMLNSpec)
      Δ ξ
      (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M Δ ξ)
  have hμ :
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Δ ξ =
        p.toMeasure.map (fun x => patch Δ x ξ) := by
    unfold StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
    unfold MarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
    unfold MarkovLogicInfiniteWorldMeasures.finiteVolumeWorldPMF
    symm
    simpa using
      (PMF.toMeasure_map (p := p) (f := fun x => patch Δ x ξ)
        (hf := measurable_patch Δ ξ))
  rw [hμ]
  rw [MeasureTheory.lintegral_map
    (μ := p.toMeasure)
    (f := fun ω : InfiniteWorld Atom =>
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S))
    (g := fun x => patch Δ x ξ)
    (StrictlyPositiveInfiniteGroundMLNSpec.measurable_finiteVolumeWorldMeasure_cylinder
      M Λ I S hS)
    (measurable_patch Δ ξ)]
  rw [MeasureTheory.lintegral_fintype]
  simpa [hμ, p, PMF.toMeasure_apply_singleton, mul_comm, mul_left_comm, mul_assoc] using
    (finiteVolumeAssignmentPMF_subregion_cylinder_dlr
      (M := M) (hΛΔ := hΛΔ) (ξ := ξ) (I := I) (S := S) hS)

/-- The target fixed-region cylinder DLR law for a global measure.

This is the next theorem layer after the current exhaustion-based convergence
results: for each fixed finite region `Λ`, the global measure is invariant under
the `Λ`-specification on every measurable cylinder event. -/
def FixedRegionCylinderDLR
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I)),
    MeasurableSet S →
      ∫⁻ ω,
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
          (MeasureTheory.cylinder I S) ∂ μ =
        μ (MeasureTheory.cylinder I S)

open Filter
open scoped Topology
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteClusterFrontend.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion

namespace RegionExhaustion

theorem MarginalClusterPoint.tendsto_lintegral_stageMarginal
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    (h : MarginalClusterPoint E M ξ μ)
    (J : Region Atom)
    (g : LocalAssignment Atom J → ENNReal)
    (hg_top : ∀ x, g x ≠ (⊤ : ENNReal)) :
    Tendsto
      (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J)
      atTop
      (nhds (∫⁻ x, g x ∂ limitMarginal μ J)) := by
  have hleft :
      (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J) =
        (fun n => ∑ x, g x * stageMarginal E M ξ n J ({x} : Set (LocalAssignment Atom J))) := by
    funext n
    simpa using
      (MeasureTheory.lintegral_fintype (μ := stageMarginal E M ξ n J) g)
  have hright :
      ∫⁻ x, g x ∂ limitMarginal μ J =
        ∑ x, g x * limitMarginal μ J ({x} : Set (LocalAssignment Atom J)) := by
    simpa using (MeasureTheory.lintegral_fintype (μ := limitMarginal μ J) g)
  rw [hleft, hright]
  refine tendsto_finset_sum (s := Finset.univ)
    (f := fun x n => g x * stageMarginal E M ξ n J ({x} : Set (LocalAssignment Atom J)))
    (a := fun x => g x * limitMarginal μ J ({x} : Set (LocalAssignment Atom J))) ?_
  intro x hx
  have hx' := h J ({x} : Set (LocalAssignment Atom J)) (MeasurableSet.singleton x)
  simpa using ENNReal.Tendsto.const_mul hx' (Or.inr (hg_top x))

theorem stageMarginal_lintegral_cylinderBoundaryKernelValue
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
    ∫⁻ x,
      StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S x
      ∂ stageMarginal E M ξ n J =
    ∫⁻ ω,
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S)
      ∂ E.finiteVolumeKernelSequence M ξ n := by
  let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
  simpa [J] using
    (calc
      ∫⁻ x,
          StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S x
          ∂ stageMarginal E M ξ n J =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
            (Finset.restrict J ω)
          ∂ E.finiteVolumeKernelSequence M ξ n := by
            simpa [stageMarginal, J] using
              (MeasureTheory.lintegral_map
                (μ := E.finiteVolumeKernelSequence M ξ n)
                (f := StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S)
                (g := Finset.restrict J)
                (by
                  classical
                  exact Measurable.of_discrete)
                (Finset.measurable_restrict J))
      _ =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
            (MeasureTheory.cylinder I S)
          ∂ E.finiteVolumeKernelSequence M ξ n := by
            apply lintegral_congr
            intro ω
            symm
            simpa [J] using
              (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_cylinderBoundaryKernelValue
                M Λ I S hS ω))

theorem limitMarginal_lintegral_cylinderBoundaryKernelValue
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (μ : Measure (InfiniteWorld Atom))
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
    ∫⁻ x,
      StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S x
      ∂ limitMarginal μ J =
    ∫⁻ ω,
      StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
        (MeasureTheory.cylinder I S)
      ∂ μ := by
  let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
  simpa [J] using
    (calc
      ∫⁻ x,
          StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S x
          ∂ limitMarginal μ J =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
            (Finset.restrict J ω)
          ∂ μ := by
            simpa [limitMarginal, J] using
              (MeasureTheory.lintegral_map
                (μ := μ)
                (f := StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S)
                (g := Finset.restrict J)
                (by
                  classical
                  exact Measurable.of_discrete)
                (Finset.measurable_restrict J))
      _ =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
            (MeasureTheory.cylinder I S)
          ∂ μ := by
            apply lintegral_congr
            intro ω
            symm
            simpa [J] using
              (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_cylinderBoundaryKernelValue
                M Λ I S hS ω))

theorem eventually_finiteVolumeKernelSequence_subregion_cylinder_dlr
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (Λ I : Region Atom)
    (S : Set (LocalAssignment Atom I))
    (hS : MeasurableSet S) :
    ∀ᶠ n in atTop,
      ∫⁻ ω,
        StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
          (MeasureTheory.cylinder I S)
        ∂ E.finiteVolumeKernelSequence M ξ n =
      E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S) := by
  rcases exists_stage_subset E Λ with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hΛn : Λ ⊆ E.region n := by
    intro a ha
    exact E.monotone hn (hN ha)
  simpa [Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence] using
    (finiteVolumeWorldMeasure_subregion_cylinder_dlr
      (M := M) (hΛΔ := hΛn) (ξ := ξ) (I := I) (S := S) hS)

theorem CylinderClusterPoint.fixedRegionCylinderDLR
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (h : CylinderClusterPoint E M ξ μ) :
    FixedRegionCylinderDLR M μ := by
  intro Λ I S hS
  let J : Region Atom := cylinderBoundarySupportRegion M.toInfiniteGroundMLNSpec Λ I
  let g : LocalAssignment Atom J → ENNReal :=
    StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue M Λ I S
  have hMarg : MarginalClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).1 h
  have hInt :
      Tendsto
        (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J)
        atTop
        (nhds (∫⁻ x, g x ∂ limitMarginal μ J)) :=
    MarginalClusterPoint.tendsto_lintegral_stageMarginal
      (h := hMarg) J g
      (fun x =>
        StrictlyPositiveInfiniteGroundMLNSpec.cylinderBoundaryKernelValue_ne_top
          M Λ I S x)
  have hTargetEq :
      ∫⁻ x, g x ∂ limitMarginal μ J =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
            (MeasureTheory.cylinder I S) ∂ μ := by
    simpa [J, g] using
      (limitMarginal_lintegral_cylinderBoundaryKernelValue
        (M := M) (μ := μ) (Λ := Λ) (I := I) (S := S) hS)
  have hInt' :
      Tendsto
        (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J)
        atTop
        (nhds
          (∫⁻ ω,
            StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
              (MeasureTheory.cylinder I S) ∂ μ)) := by
    simpa [hTargetEq] using hInt
  have hevent :
      (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J)
        =ᶠ[atTop]
      (fun n => E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S)) := by
    filter_upwards
      [eventually_finiteVolumeKernelSequence_subregion_cylinder_dlr
        (E := E) (M := M) (ξ := ξ) (Λ := Λ) (I := I) (S := S) hS] with n hn
    calc
      ∫⁻ x, g x ∂ stageMarginal E M ξ n J
          =
        ∫⁻ ω,
          StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure M Λ ω
            (MeasureTheory.cylinder I S) ∂ E.finiteVolumeKernelSequence M ξ n := by
              simpa [J, g] using
                (stageMarginal_lintegral_cylinderBoundaryKernelValue
                  (E := E) (M := M) (ξ := ξ) (n := n)
                  (Λ := Λ) (I := I) (S := S) hS)
      _ = E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S) := hn
  have hCyl :
      Tendsto
        (fun n => E.finiteVolumeKernelSequence M ξ n (MeasureTheory.cylinder I S))
        atTop
        (nhds (μ (MeasureTheory.cylinder I S))) :=
    h I S hS
  have hCyl' :
      Tendsto
        (fun n => ∫⁻ x, g x ∂ stageMarginal E M ξ n J)
        atTop
        (nhds (μ (MeasureTheory.cylinder I S))) := by
    exact hCyl.congr' hevent.symm
  exact tendsto_nhds_unique hInt' hCyl'

theorem MarginalClusterPoint.fixedRegionCylinderDLR
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (h : MarginalClusterPoint E M ξ μ) :
    FixedRegionCylinderDLR M μ := by
  have hcyl : CylinderClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).2 h
  exact CylinderClusterPoint.fixedRegionCylinderDLR hcyl

theorem projectiveLimitMeasure_fixedRegionCylinderDLR_of_eq
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hEq : projectiveLimitMeasure (Atom := Atom) e P hP = μ) :
    FixedRegionCylinderDLR M
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  simpa [hEq] using
    (CylinderClusterPoint.fixedRegionCylinderDLR
      (E := E) (M := M) (ξ := ξ) (μ := μ) hμ)

theorem projectiveLimitMeasure_fixedRegionCylinderDLR_of_limitMarginal_eq
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : CylinderClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    FixedRegionCylinderDLR M
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hEq := projectiveLimitMeasure_eq_of_limitMarginal_eq
    (Atom := Atom) (μ := μ) e P hP hPμ
  exact projectiveLimitMeasure_fixedRegionCylinderDLR_of_eq
    (E := E) (M := M) (ξ := ξ) (μ := μ) hμ e P hP hEq

theorem projectiveLimitMeasure_fixedRegionCylinderDLR_of_marginalClusterPoint
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {μ : Measure (InfiniteWorld Atom)}
    [IsProbabilityMeasure μ]
    (hμ : MarginalClusterPoint E M ξ μ)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hPμ : ∀ I, P I = limitMarginal μ I) :
    FixedRegionCylinderDLR M
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  have hcyl : CylinderClusterPoint E M ξ μ :=
    (cylinderClusterPoint_iff_marginalClusterPoint E M ξ μ).2 hμ
  exact projectiveLimitMeasure_fixedRegionCylinderDLR_of_limitMarginal_eq
    (E := E) (M := M) (ξ := ξ) (μ := μ) hcyl e P hP hPμ

/-- If the stage marginals converge pointwise on measurable finite-dimensional
sets to a projective family `P`, then the canonical projective-limit measure
built from `P` is already a marginal cluster point of the finite-volume
sequence. -/
theorem marginalClusterPoint_projectiveLimitMeasure_of_stageMarginal_tendsto
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hconv : ∀ (I : Finset Atom) (S : Set (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i)),
        MeasurableSet S →
          Tendsto (fun n => stageMarginal E M ξ n I S) atTop (nhds (P I S))) :
    MarginalClusterPoint E M ξ
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  intro I S hS
  have hI :
      ((projectiveLimitMeasure (Atom := Atom) e P hP).map I.restrict) = P I := by
    simpa [limitMarginal] using
      (limitMarginal_projectiveLimitMeasure (Atom := Atom) e P hP I)
  simpa [hI] using hconv I S hS

/-- Therefore a limiting projective family of stage marginals already yields a
global fixed-region cylinder DLR measure via the canonical countable
projective-limit construction. -/
theorem projectiveLimitMeasure_fixedRegionDLR_of_stageMarginal_tendsto
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hconv : ∀ (I : Finset Atom) (S : Set (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i)),
        MeasurableSet S →
          Tendsto (fun n => stageMarginal E M ξ n I S) atTop (nhds (P I S))) :
    FixedRegionCylinderDLR M
      (projectiveLimitMeasure (Atom := Atom) e P hP) := by
  exact MarginalClusterPoint.fixedRegionCylinderDLR
    (E := E) (M := M) (ξ := ξ)
    (μ := projectiveLimitMeasure (Atom := Atom) e P hP)
    (marginalClusterPoint_projectiveLimitMeasure_of_stageMarginal_tendsto
      (E := E) (M := M) (ξ := ξ) e P hP hconv)

/-- Existence packaging at the current theorem frontier: any projective family
appearing as the pointwise measurable limit of the stage marginals gives rise
to a global fixed-region cylinder DLR measure.  The remaining gap to the
Singla--Domingos existence theorem is therefore the compactness/extraction step
that produces such a limiting family from local finiteness. -/
theorem exists_fixedRegionCylinderDLR_of_stageMarginal_tendsto
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I,
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hconv : ∀ (I : Finset Atom) (S : Set (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i)),
        MeasurableSet S →
          Tendsto (fun n => stageMarginal E M ξ n I S) atTop (nhds (P I S))) :
    ∃ μ : Measure (InfiniteWorld Atom),
      ∃ _ : IsProbabilityMeasure μ, FixedRegionCylinderDLR M μ := by
  refine ⟨projectiveLimitMeasure (Atom := Atom) e P hP, inferInstance, ?_⟩
  exact projectiveLimitMeasure_fixedRegionDLR_of_stageMarginal_tendsto
    (E := E) (M := M) (ξ := ξ) e P hP hconv

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
